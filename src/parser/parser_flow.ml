(*
 * Copyright (c) 2013-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the "flow" directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 *
 *)

open Lexer_flow
open Parser_env
module Ast = Spider_monkey_ast
open Ast
module Error = Parse_error
module SSet = Set.Make(String)
module SMap = Map.Make(String)
let is_future_reserved = function
  | "enum" -> true
  | _ -> false

let is_strict_reserved = function
  | "interface"
  | "implements"
  | "package"
  | "private"
  | "protected"
  | "public"
  | "static"
  | "yield" -> true
  | _ -> false

let is_restricted = function
  | "eval"
  | "arguments" -> true
  | _ -> false

let name_of_id id =
  let (_, {Identifier.name; _;}) = id in
  name

(* Answer questions about what comes next *)
module Peek = struct
  open Loc

  (* If you're looping waiting for a token, then use token_loop instead. *)
  let token ?(i=0) env = (lookahead ~i env).lex_token
  let value ?(i=0) env = (lookahead ~i env).lex_value
  let loc ?(i=0) env = (lookahead ~i env).lex_loc

  (* True if there is a line terminator before the next token *)
  let line_terminator env =
    match last_loc env with
      | None -> false
      | Some loc' ->
          (loc env).start.line > loc'.start.line

  let is_implicit_semicolon env =
    match token env with
    | T_EOF | T_RCURLY -> true
    | T_SEMICOLON -> false
    | _ -> line_terminator env

  let semicolon_loc ?(i=0) env =
    if token ~i env = T_SEMICOLON
    then Some (loc ~i env)
    else None

  (* This returns true if the next token is identifier-ish (even if it is an
   * error) *)
  let identifier ?(i=0) env =
    let name = value ~i env in
    match token ~i env with
    | _ when
      is_strict_reserved name ||
      is_restricted name ||
      is_future_reserved name-> true
    | T_LET
    | T_TYPE
    | T_OF
    | T_DECLARE
    | T_ASYNC
    | T_AWAIT
    | T_IDENTIFIER -> true
    | _ -> false

  let _function ?(i=0) env =
    token ~i env = T_FUNCTION ||
    (token ~i env = T_ASYNC && token ~i:(i+1) env = T_FUNCTION)

  let _class ?(i=0) env =
    match token ~i env with
    | T_CLASS
    | T_AT -> true
    | _ -> false
end

(*****************************************************************************)
(* Errors *)
(*****************************************************************************)

(* Complains about an error at the location of the lookahead *)
let error env e =
  let loc = Peek.loc env in
  error_at env (loc, e)

let strict_error env e : env =
  if strict env then error env e
  else env

let strict_error_at env (loc, e) : env =
  if strict env then error_at env (loc, e)
  else env

(* Sometimes we add the same error for multiple different reasons. This is hard
   to avoid, so instead we just filter the duplicates out. This function takes
   a reversed list of errors and returns the list in forward order with dupes
   removed. This differs from a set because the original order is preserved. *)
let filter_duplicate_errors =
  let module ErrorSet = Set.Make(struct
    type t = Loc.t * Error.t
    let compare (a_loc, a_error) (b_loc, b_error) =
      let loc = Loc.compare a_loc b_loc in
      if loc = 0
      then Pervasives.compare a_error b_error
      else loc
  end) in
  fun errs ->
    let errs = List.rev errs in
    let _, deduped = List.fold_left (fun (set, deduped) err ->
      if ErrorSet.mem err set then (set, deduped)
      else (ErrorSet.add err set, err::deduped)
    ) (ErrorSet.empty, []) errs in
    List.rev deduped

let get_unexpected_error = function
  | T_EOF, _ -> Error.UnexpectedEOS
  | T_NUMBER _, _ -> Error.UnexpectedNumber
  | T_JSX_TEXT _, _
  | T_STRING _, _ -> Error.UnexpectedString
  | T_IDENTIFIER, _ -> Error.UnexpectedIdentifier
  | _, word when is_future_reserved word -> Error.UnexpectedReserved
  | _, word when is_strict_reserved word -> Error.StrictReservedWord
  | _, value -> Error.UnexpectedToken value

let error_unexpected env =
  let lookahead = lookahead env in
  (* So normally we consume the lookahead lex result when Eat.advance is
   * called, which will add any lexing errors to our list of errors. However,
   * raising an unexpected error for a lookahead is kind of like consuming that
   * token, so we should process any lexing errors before complaining about the
   * unexpected token *)
  let env = error_list env (lookahead.lex_errors) in
  error env (get_unexpected_error (lookahead.lex_token, lookahead.lex_value))

let error_on_decorators env decorators : env =
  List.fold_left (fun env decorator ->
    error_at env ((fst decorator), Error.UnsupportedDecorator)
  ) env decorators

(* Consume zero or more tokens *)
module Eat : sig
  val advance : env -> lex_env * lex_result -> unit
  val token : env -> unit
  val push_lex_mode : env -> lex_mode -> unit
  val pop_lex_mode : env -> unit
  val double_pop_lex_mode : env -> unit
  val semicolon : env -> env
end = struct
  let advance = Parser_env.advance

  (* TODO should this be in Parser_env? *)
  (* Consume a single token *)
  let token env =
    let last = lex_env env, lookahead env in
    advance env last

  let push_lex_mode = Parser_env.push_lex_mode
  let pop_lex_mode = Parser_env.pop_lex_mode
  let double_pop_lex_mode = Parser_env.double_pop_lex_mode

  (* Semicolon insertion is handled here :(. There seem to be 2 cases where
  * semicolons are inserted. First, if we reach the EOF. Second, if the next
  * token is } or is separated by a LineTerminator.
  *)
  let semicolon env =
    if not (Peek.is_implicit_semicolon env) then
      if Peek.token env = T_SEMICOLON then begin token env; env end
      else error_unexpected env
    else env
end

module Expect = struct
  let token env t =
    let env = if Peek.token env <> t then error_unexpected env else env in
    Eat.token env

  (* If the next token is t, then eat it and return true
   * else return false *)
  let maybe env t =
    if Peek.token env = t
    then begin
      Eat.token env;
      true
    end else false

  let contextual env str =
    let env = if Peek.value env <> str then error_unexpected env else env in
    Eat.token env
end

let with_loc (fn: env -> env * 'a) (env: env) : env * Loc.t * 'a =
  let start_loc = Peek.loc env in
  let env, result = fn env in
  let end_loc = match last_loc env with
  | Some loc -> loc
  | None ->
      let env = error env (Error.Assertion "did not consume any tokens") in
      Peek.loc env
  in
  env, Loc.btwn start_loc end_loc, result

module rec Parse : sig
  val program : env -> env * Ast.program
  val statement : env -> env * Ast.Statement.t
  val statement_list_item : ?decorators:Ast.Expression.t list -> env -> env * Ast.Statement.t
  val statement_list : term_fn:(token->bool) -> env -> env * Ast.Statement.t list
  val statement_list_with_directives : term_fn:(token->bool) -> env -> env * Ast.Statement.t list * bool
  val module_body : term_fn:(token->bool) -> env -> env * Ast.Statement.t list
  val expression : env -> env * Ast.Expression.t
  val assignment : env -> env * Ast.Expression.t
  val object_initializer : env -> env * Ast.Expression.Object.t
  val array_initializer : env -> env * Ast.Expression.Array.t
  val identifier : ?restricted_error:Error.t -> env -> env * Ast.Identifier.t
  val identifier_or_reserved_keyword : env -> env * Ast.Identifier.t * (Loc.t * Error.t) option
  val identifier_with_type : env -> Error.t -> env * Ast.Identifier.t
  val block_body : env -> env * (Loc.t * Ast.Statement.Block.t)
  val function_block_body : env -> env * Loc.t * Ast.Statement.Block.t * bool
  val jsx_element : env -> env * (Loc.t * Ast.JSX.element)
  val pattern : env -> Error.t -> env * Ast.Pattern.t
  val pattern_from_expr : env -> Ast.Expression.t -> env * Ast.Pattern.t
  val object_key : env -> env * (Loc.t * Ast.Expression.Object.Property.key)
  val class_declaration : env -> Ast.Expression.t list -> env * Ast.Statement.t
  val class_expression : env -> env * Ast.Expression.t
  val is_assignable_lhs : Ast.Expression.t -> bool
end = struct
  module Type : sig
    val _type : env -> Ast.Type.t
    val type_parameter_declaration : env -> Ast.Type.ParameterDeclaration.t option
    val type_parameter_declaration_with_defaults : env -> Ast.Type.ParameterDeclaration.t option
    val type_parameter_instantiation : env -> Ast.Type.ParameterInstantiation.t option
    val generic : env -> Loc.t * Ast.Type.Generic.t
    val _object : ?allow_static:bool -> env -> env * (Loc.t * Type.Object.t)
    val function_param_list : env -> Type.Function.Param.t option * Type.Function.Param.t list
    val annotation : env -> Ast.Type.annotation
    val annotation_opt : env -> Ast.Type.annotation option
  end = struct
    type param_list_or_type =
      | ParamList of (Type.Function.Param.t option * Type.Function.Param.t list)
      | Type of Type.t

    let rec _type env = union env

    and annotation env =
      let env = if not (should_parse_types env)
        then error env Error.UnexpectedTypeAnnotation
        else env in
      let start_loc = Peek.loc env in
      Expect.token env T_COLON;
      let typeAnnotation = _type env in
      let end_loc = match last_loc env with
      | Some loc -> loc
      | None -> assert false in
      Loc.btwn start_loc end_loc, typeAnnotation

    and rev_nonempty_acc acc =
      let end_loc = match acc with
      | (loc, _)::_ -> loc
      | _ -> assert false in
      let acc = List.rev acc in
      let start_loc = match acc with
      | (loc, _)::_ -> loc
      | _ -> assert false in
      Loc.btwn start_loc end_loc, acc

    and union env =
      let left = intersection env in
      union_with env left

    and union_with =
      let rec unions env acc =
        match Peek.token env with
        | T_BIT_OR ->
            Expect.token env T_BIT_OR;
            unions env (intersection env::acc)
        | _ ->
            let loc, acc = rev_nonempty_acc acc in
            loc, Type.Union acc
      in fun env left ->
        if Peek.token env = T_BIT_OR
        then unions env [left]
        else left

    and intersection env =
      let left = prefix env in
      intersection_with env left

    and intersection_with =
      let rec intersections env acc =
        match Peek.token env with
        | T_BIT_AND ->
            Expect.token env T_BIT_AND;
            intersections env (prefix env::acc)
        | _ ->
            let loc, acc = rev_nonempty_acc acc in
            loc, Type.Intersection acc
      in fun env left ->
        if Peek.token env = T_BIT_AND
        then intersections env [left]
        else left

    and prefix env =
      match Peek.token env with
      | T_PLING ->
          let loc = Peek.loc env in
          Expect.token env T_PLING;
          let t = prefix env in
          Loc.btwn loc (fst t), Type.Nullable t
      | _ ->
          postfix env

    and postfix env =
      let env, t = primary env in
      postfix_with env t

    and postfix_with env t =
      if Expect.maybe env T_LBRACKET
      then begin
        let end_loc = Peek.loc env in
        Expect.token env T_RBRACKET;
        let loc = Loc.btwn (fst t) end_loc in
        let t = loc, Type.Array t in
        postfix_with env t
      end else t

    and primary (env: env) : env * Ast.Type.t =
      let loc = Peek.loc env in
      match Peek.token env with
      | T_MULT ->
          Expect.token env T_MULT;
          env, (loc, Type.Exists)
      | T_LESS_THAN -> _function env
      | T_LPAREN ->
          let t = function_or_group env in
          env, t
      | T_LCURLY ->
          let env, (loc, o) = _object env in
          env, (loc, Type.Object o)
      | T_TYPEOF ->
          let start_loc = Peek.loc env in
          Expect.token env T_TYPEOF;
          let env, t = primary env in
          env, (Loc.btwn start_loc (fst t), Type.Typeof t)
      | T_LBRACKET ->
          let t = tuple env in
          env, t
      | T_IDENTIFIER ->
          let loc, g = generic env in
          env, (loc, Type.Generic g)
      | T_STRING (loc, value, raw, octal)  ->
          let env = if octal
            then strict_error env Error.StrictOctalLiteral
            else env in
          Expect.token env (T_STRING (loc, value, raw, octal));
          env, (loc, Type.(StringLiteral StringLiteral.({
            value;
            raw;
          })))
      | T_NUMBER_SINGLETON_TYPE (number_type, value) ->
          let raw = Peek.value env in
          Expect.token env (T_NUMBER_SINGLETON_TYPE (number_type, value));
          let env = if number_type = LEGACY_OCTAL
            then strict_error env Error.StrictOctalLiteral
            else env in
          env, (loc, Type.(NumberLiteral NumberLiteral.({
            value;
            raw;
          })))
      | (T_TRUE | T_FALSE) as token ->
          let raw = Peek.value env in
          Expect.token env token;
          let value = token = T_TRUE in
          env, (loc, Type.(BooleanLiteral BooleanLiteral.({
            value;
            raw;
          })))
      | token ->
          match primitive token with
          | Some t ->
              Expect.token env token;
              env, (loc, t)
          | None ->
              let env = error_unexpected env in
              env, (loc, Type.Any)

    and primitive = function
      | T_ANY_TYPE     -> Some Type.Any
      | T_BOOLEAN_TYPE -> Some Type.Boolean
      | T_NUMBER_TYPE  -> Some Type.Number
      | T_STRING_TYPE  -> Some Type.String
      | T_VOID_TYPE    -> Some Type.Void
      | T_NULL         -> Some Type.Null
      | _ -> None

    and tuple =
      let rec types env acc =
        match Peek.token env with
        | T_EOF
        | T_RBRACKET -> List.rev acc
        | _ ->
            let acc = (_type env)::acc in
            (* Trailing comma support (like [number, string,]) *)
            if Peek.token env <> T_RBRACKET then Expect.token env T_COMMA;
            types env acc

      in fun env ->
        let start_loc = Peek.loc env in
        Expect.token env T_LBRACKET;
        let tl = types env [] in
        let end_loc = Peek.loc env in
        Expect.token env T_RBRACKET;
        Loc.btwn start_loc end_loc, Type.Tuple tl

    and function_param_with_id env name =
      let env = if not (should_parse_types env)
        then error env Error.UnexpectedTypeAnnotation
        else env in
      let optional = Expect.maybe env T_PLING in
      Expect.token env T_COLON;
      let typeAnnotation = _type env in
      Loc.btwn (fst name) (fst typeAnnotation), Type.Function.Param.({
        name;
        typeAnnotation;
        optional;
      })

    and function_param_list_without_parens =
      let param env =
        let env, name, _ = Parse.identifier_or_reserved_keyword env in
        function_param_with_id env name

      in let rec param_list env acc =
        match Peek.token env with
        | T_EOF
        | T_ELLIPSIS
        | T_RPAREN as t ->
            let rest = if t = T_ELLIPSIS
            then begin
              Expect.token env T_ELLIPSIS;
              Some (param env)
            end else None in
            rest, List.rev acc
        | _ ->
          let acc = (param env)::acc in
          if Peek.token env <> T_RPAREN
          then Expect.token env T_COMMA;
          param_list env acc

      in fun env -> param_list env

    and function_param_list env =
        Expect.token env T_LPAREN;
        let ret = function_param_list_without_parens env [] in
        Expect.token env T_RPAREN;
        ret

    and param_list_or_type env =
      Expect.token env T_LPAREN;
      let ret = match Peek.token env with
      | T_EOF
      | T_ELLIPSIS ->
          (* (... is definitely the beginning of a param list *)
          ParamList (function_param_list_without_parens env [])
      | T_RPAREN ->
          (* () or is definitely a param list *)
          ParamList (None, [])
      | T_IDENTIFIER ->
          (* This could be a function parameter or a generic type *)
          function_param_or_generic_type env
      | token ->
          (match primitive token with
          | None ->
              (* All params start with an identifier or `...` *)
              Type (_type env)
          | Some _ ->
              (* Don't know if this is (number) or (number: number). The first
               * is a type, the second is a param. *)
              match Peek.token ~i:1 env with
              | T_PLING | T_COLON ->
                (* Ok this is definitely a parameter *)
                let env, name, _ = Parse.identifier_or_reserved_keyword env in
                let env = if not (should_parse_types env)
                  then error env Error.UnexpectedTypeAnnotation
                  else env in
                let optional = Expect.maybe env T_PLING in
                Expect.token env T_COLON;
                let typeAnnotation = _type env in
                if Peek.token env <> T_RPAREN
                then Expect.token env T_COMMA;
                let param = Loc.btwn (fst name) (fst typeAnnotation), Type.Function.Param.({
                  name;
                  typeAnnotation;
                  optional;
                }) in
                ParamList (function_param_list_without_parens env [param])
              | _ ->
                Type (_type env)
          )
      in
      Expect.token env T_RPAREN;
      ret

    and function_param_or_generic_type env =
      let env, id = Parse.identifier env in
      match Peek.token env with
      | T_PLING (* optional param *)
      | T_COLON ->
          let param = function_param_with_id env id in
          ignore (Expect.maybe env T_COMMA);
          ParamList (function_param_list_without_parens env [param])
      | _ ->
          Type (union_with env
                  (intersection_with env
                    (postfix_with env (generic_type_with_identifier env id)))
                )

    and function_or_group env =
      let start_loc = Peek.loc env in
      match param_list_or_type env with
      | ParamList (rest, params) ->
        Expect.token env T_ARROW;
        let returnType = _type env in
        let end_loc = fst returnType in
        Loc.btwn start_loc end_loc, Type.(Function Function.({
          params;
          returnType;
          rest;
          typeParameters = None;
        }))
      | Type _type -> _type

    and _function env =
      let start_loc = Peek.loc env in
      let typeParameters = type_parameter_declaration ~allow_default:false env in
      let rest, params = function_param_list env in
      Expect.token env T_ARROW;
      let returnType = _type env in
      let end_loc = fst returnType in
      env, (Loc.btwn start_loc end_loc, Type.(Function Function.({
        params;
        returnType;
        rest;
        typeParameters;
      })))

    and _object : ?allow_static:bool -> env -> env * (Loc.t * Type.Object.t) =
      let methodish env start_loc =
        let typeParameters = type_parameter_declaration ~allow_default:false env in
        let rest, params = function_param_list env in
        Expect.token env T_COLON;
        let returnType = _type env in
        let loc = Loc.btwn start_loc (fst returnType) in
        loc, Type.Function.({
          params;
          returnType;
          rest;
          typeParameters;
        })

      in let method_property env start_loc static key =
        let value = methodish env start_loc in
        let value = fst value, Type.Function (snd value) in
        fst value, Type.Object.Property.({
          key;
          value;
          optional = false;
          static;
          _method = true;
        })

      in let call_property env start_loc static =
        let value = methodish env (Peek.loc env) in
        Loc.btwn start_loc (fst value), Type.Object.CallProperty.({
          value;
          static;
        })

      in let property env start_loc static key =
        let env = if not (should_parse_types env)
          then error env Error.UnexpectedTypeAnnotation
          else env in
        let optional = Expect.maybe env T_PLING in
        Expect.token env T_COLON;
        let value = _type env in
        Loc.btwn start_loc (fst value), Type.Object.Property.({
          key;
          value;
          optional;
          static;
          _method = false;
        })

      in let indexer_property env start_loc static =
        Expect.token env T_LBRACKET;
        let env, id, _ = Parse.identifier_or_reserved_keyword env in
        Expect.token env T_COLON;
        let key = _type env in
        Expect.token env T_RBRACKET;
        Expect.token env T_COLON;
        let value = _type env in
        Loc.btwn start_loc (fst value), Type.Object.Indexer.({
          id;
          key;
          value;
          static;
        })

      in let semicolon (env: env) : env =
        match Peek.token env with
        | T_COMMA | T_SEMICOLON -> Eat.token env; env
        | T_RCURLY -> env
        | _ -> error_unexpected env

      in let rec properties ~allow_static env (acc, indexers, callProperties) =
        let start_loc = Peek.loc env in
        let static = allow_static && Expect.maybe env T_STATIC in
        match Peek.token env with
        | T_EOF
        | T_RCURLY -> List.rev acc, List.rev indexers, List.rev callProperties
        | T_LBRACKET ->
          let indexer = indexer_property env start_loc static in
          let env = semicolon env in
          properties allow_static env (acc, indexer::indexers, callProperties)
        | T_LESS_THAN
        | T_LPAREN ->
          let call_prop = call_property env start_loc static in
          let env = semicolon env in
          properties allow_static env (acc, indexers, call_prop::callProperties)
        | _ ->
          let env, static, (_, key) = match static, Peek.token env with
          | true, T_COLON ->
              let env =
                strict_error_at env (start_loc, Error.StrictReservedWord) in
              let static_key =
                start_loc, Expression.Object.Property.Identifier ( start_loc, {
                  Identifier.name = "static";
                  optional = false;
                  typeAnnotation = None;
                }) in
              env, false, static_key
          | _ ->
              Eat.push_lex_mode env NORMAL_LEX;
              let env, key = Parse.object_key env in
              Eat.pop_lex_mode env;
              env, static, key
          in
          let property = match Peek.token env with
          | T_LESS_THAN
          | T_LPAREN -> method_property env start_loc static key
          | _ -> property env start_loc static key in
          let env = semicolon env in
          properties allow_static env (property::acc, indexers, callProperties)

      in fun ?(allow_static=false) env ->
        let start_loc = Peek.loc env in
        Expect.token env T_LCURLY;
        let properties, indexers, callProperties =
          properties ~allow_static env ([], [], []) in
        let end_loc = Peek.loc env in
        Expect.token env T_RCURLY;
        let loc = Loc.btwn start_loc end_loc in
        env, (loc, Type.Object.({
          properties;
          indexers;
          callProperties
        }))

    and type_parameter_declaration =
      let rec params env ~allow_default ~require_default acc = Type.ParameterDeclaration.TypeParam.(
        let variance = match Peek.token env with
          | T_PLUS -> Eat.token env; Some Variance.Plus
          | T_MINUS -> Eat.token env; Some Variance.Minus
          | _ -> None in
        let env, (loc, id) =
          Parse.identifier_with_type env Error.StrictParamName in
        let env, default, require_default =
          match allow_default, Peek.token env with
          | false, _ -> env, None, false
          | true, T_ASSIGN ->
            Eat.token env;
            env, Some (_type env), true
          | true, _ ->
            let env = if require_default
              then error_at env (loc, Error.MissingTypeParamDefault)
              else env in
            env, None, require_default
        in
        let param = loc, {
          name = id.Identifier.name;
          bound = id.Identifier.typeAnnotation;
          variance;
          default;
        } in
        let acc = param::acc in
        match Peek.token env with
        | T_EOF
        | T_GREATER_THAN -> List.rev acc
        | _ ->
          Expect.token env T_COMMA;
          if Peek.token env = T_GREATER_THAN
          then List.rev acc
          else params env ~allow_default ~require_default acc
      )
      in fun ~allow_default env ->
          let start_loc = Peek.loc env in
          if Peek.token env = T_LESS_THAN
          then begin
            let env = if not (should_parse_types env)
              then error env Error.UnexpectedTypeAnnotation
              else env in
            Expect.token env T_LESS_THAN;
            let params = params env ~allow_default ~require_default:false [] in
            let loc = Loc.btwn start_loc (Peek.loc env) in
            Expect.token env T_GREATER_THAN;
            Some (loc, Type.ParameterDeclaration.({
              params;
            }))
          end else None

    and type_parameter_instantiation =
      let rec params env acc =
        match Peek.token env with
        | T_EOF
        | T_GREATER_THAN -> List.rev acc
        | _ ->
          let acc = (_type env)::acc in
          if Peek.token env <> T_GREATER_THAN
          then Expect.token env T_COMMA;
          params env acc

      in fun env ->
          let start_loc = Peek.loc env in
          if Peek.token env = T_LESS_THAN
          then begin
            Expect.token env T_LESS_THAN;
            let params = params env [] in
            let loc = Loc.btwn start_loc (Peek.loc env) in
            Expect.token env T_GREATER_THAN;
            Some (loc, Type.ParameterInstantiation.({
              params;
            }))
          end else None

    and generic env =
      let env, id = Parse.identifier env in
      raw_generic_with_identifier env id

    and raw_generic_with_identifier =
      let rec identifier env (q_loc, qualification) =
        if Peek.token env = T_PERIOD
        then begin
          Expect.token env T_PERIOD;
          let env, id = Parse.identifier env in
          let loc = Loc.btwn q_loc (fst id) in
          let qualification = Type.Generic.Identifier.(Qualified (loc, {
            qualification;
            id;
          })) in
          identifier env (loc, qualification)
        end else (q_loc, qualification)

      in fun env id ->
        let id = fst id, Type.Generic.Identifier.Unqualified id in
        let id_loc, id = identifier env id in
        let typeParameters = type_parameter_instantiation env in
        let loc = match typeParameters with
        | None -> id_loc
        | Some (loc, _) -> Loc.btwn id_loc loc in
        loc, Type.Generic.({
          id;
          typeParameters;
        })

    and generic_type_with_identifier env id =
      let loc, generic = raw_generic_with_identifier env id in
      loc, Type.Generic generic

    and annotation_opt env =
      match Peek.token env with
      | T_COLON -> Some (annotation env)
      | _ -> None

    let wrap f env =
      let env = env |> with_strict true in
      Eat.push_lex_mode env TYPE_LEX;
      let ret = f env in
      Eat.pop_lex_mode env;
      ret

    let _type = wrap _type
    let type_parameter_declaration_with_defaults =
      wrap (type_parameter_declaration ~allow_default:true)
    let type_parameter_declaration =
      wrap (type_parameter_declaration ~allow_default:false)
    let type_parameter_instantiation = wrap type_parameter_instantiation
    let _object ?(allow_static=false) env = wrap (_object ~allow_static) env
    let function_param_list = wrap function_param_list
    let annotation = wrap annotation
    let annotation_opt = wrap annotation_opt
    let generic = wrap generic
  end

  module Declaration = struct
    let check_param =
      let rec pattern ((env, x) as check_env) (loc, p) = Pattern.(match p with
        | Object o -> _object check_env o
        | Array arr -> _array check_env arr
        | Assignment { Assignment.left; _ } -> pattern check_env left
        | Identifier id -> identifier check_env id
        | Expression _ -> (
            let env =
              error_at env (loc, Error.ExpectedPatternFoundExpression) in
            (env, x)
          )
      )

      and _object check_env o =
        List.fold_left
          object_property
          check_env
          o.Pattern.Object.properties

      and object_property check_env = Pattern.Object.(function
        | Property (_, property) -> Property.(
            let check_env = match property.key with
            | Identifier id -> identifier_no_dupe_check check_env id
            | _ -> check_env in
            pattern check_env property.pattern)
        | SpreadProperty (_, { SpreadProperty.argument; }) ->
            pattern check_env argument)

      and _array check_env arr =
        List.fold_left
        array_element
        check_env
        arr.Pattern.Array.elements

      and array_element check_env = Pattern.Array.(function
        | None -> check_env
        | Some (Element p) -> pattern check_env p
        | Some (Spread (_, { SpreadElement.argument; })) ->
            pattern check_env argument)

      and identifier (env, param_names) (loc, { Identifier.name; _ } as id) =
        let env = if SSet.mem name param_names
          then error_at env (loc, Error.StrictParamDupe)
          else env in
        let env, param_names =
          identifier_no_dupe_check (env, param_names) id in
        env, SSet.add name param_names

      and identifier_no_dupe_check (env, param_names) (loc, { Identifier.name; _ }) =
        let env = if is_restricted name
          then strict_error_at env (loc, Error.StrictParamName)
          else env in
        let env = if is_future_reserved name || is_strict_reserved name
          then strict_error_at env (loc, Error.StrictReservedWord)
          else env in
        env, param_names

      in pattern

    (* Strict is true if we were already in strict mode or if we are newly in
     * strict mode due to a directive in the function.
     * Simple is the IsSimpleParameterList thing from the ES6 spec *)
    let strict_post_check env ~strict ~simple id params =
      if strict || not simple
      then
        (* If we are doing this check due to strict mode than there are two
         * cases to consider. The first is when we were already in strict mode
         * and therefore already threw strict errors. In this case we want to
         * do these checks outside of strict mode. The other is if we
         * originally parsed in non-strict mode but now are strict. Then we
         * want to do these checks in strict mode *)
        let env =
          if strict
          then env |> with_strict (not (Parser_env.strict env))
          else env in
        let env = match id with
        | Some (loc, { Identifier.name; _ }) ->
            let env = if is_restricted name
              then strict_error_at env (loc, Error.StrictFunctionName)
              else env in
            let env = if is_future_reserved name || is_strict_reserved name
              then strict_error_at env (loc, Error.StrictReservedWord)
              else env in
            env
        | None -> env
        in
        (* TODO: return env *)
        ignore (List.fold_left check_param (env, SSet.empty) params)

    let function_params : env -> env * Ast.Pattern.t list * Ast.Expression.t option list * Ast.Identifier.t option =
      let rec param env : env * Ast.Pattern.t * Ast.Expression.t option =
        let env, id = Parse.pattern env Error.StrictParamName in
        if Peek.token env = T_ASSIGN
        then begin
          Expect.token env T_ASSIGN;
          let env, default = Parse.assignment env in
          env, id, Some default
        end else
          env, id, None
      and param_list (
        (env: env),
        (params: Ast.Pattern.t list),
        (defaults: Ast.Expression.t option list),
        (has_default: bool)
      ) : env * Ast.Pattern.t list * Ast.Expression.t option list * Ast.Identifier.t option =
        match Peek.token env with
        | T_EOF
        | T_RPAREN
        | T_ELLIPSIS as t ->
            let env, rest =
              if t = T_ELLIPSIS then begin
                Expect.token env T_ELLIPSIS;
                let env, id =
                  Parse.identifier_with_type env Error.StrictParamName in
                env, Some id
              end else
                env, None
            in
            let env = if Peek.token env <> T_RPAREN
              then error env Error.ParameterAfterRestParameter
              else env in
            let defaults = if has_default then List.rev defaults else [] in
            env, List.rev params, defaults, rest
        | _ ->
            let env, param, default = param env in
            let has_default = has_default || default <> None in
            if Peek.token env <> T_RPAREN
            then Expect.token env T_COMMA;
            param_list (env, param::params, default::defaults, has_default)

      in fun env ->
        Expect.token env T_LPAREN;
        let env, params, defaults, rest = param_list (env, [], [], false) in
        Expect.token env T_RPAREN;
        env, params, defaults, rest

    let function_body
        (env: env) ~(async: bool) ~(generator: bool)
        : env * (Loc.t * Ast.Function.body * bool) =
      let prev_env = env in
      let env = enter_function env ~async ~generator in
      let env, loc, block, strict = Parse.function_block_body env in
      let env = leave_function ~prev_env env in
      env, (loc, Function.BodyBlock (loc, block), strict)

    let concise_function_body
        (env: env) ~(async: bool) ~(generator: bool)
        : env * (Ast.Function.body * bool) =
      let prev_in_function = in_function env in
      let env = env |> with_in_function true in
      let env, ret = match Peek.token env with
      | T_LCURLY ->
          let env, (_, body, strict) = function_body env ~async ~generator in
          env, (body, strict)
      | _ ->
          let prev_env = env in
          let env = enter_function env ~async ~generator in
          let env, expr = Parse.assignment env in
          let is_strict = strict env in
          let env = leave_function ~prev_env env in
          env, (Function.BodyExpression expr, is_strict)
      in
      let env = env |> with_in_function prev_in_function in
      env, ret

    let generator env is_async : env * bool =
      match is_async, Expect.maybe env T_MULT with
      | true, true ->
          let env = error env Error.AsyncGenerator in
          env, true
      | _, result -> env, result

    let async env = Expect.maybe env T_ASYNC

    let is_simple_function_params =
      let is_simple_param = function
      | _, Pattern.Identifier _ ->  true
      | _ -> false

      in fun params defaults rest ->
        defaults = [] && rest = None && List.for_all is_simple_param params

    let _function env =
      let start_loc = Peek.loc env in
      let async = async env in
      Expect.token env T_FUNCTION;
      let env, generator = generator env async in
      let env, typeParameters, id = (
        match in_export env, Peek.token env with
        | true, T_LPAREN -> env, None, None
        | true, T_LESS_THAN ->
          let typeParams = Type.type_parameter_declaration env in
          let env, id =
            if Peek.token env = T_LPAREN then env, None
            else
              let env, id =
                Parse.identifier ~restricted_error:Error.StrictFunctionName env
              in
              env, Some id
          in
          env, typeParams, id
        | _ ->
          let env, id =
            Parse.identifier ~restricted_error:Error.StrictFunctionName env
          in
          env, Type.type_parameter_declaration env, Some id
      ) in
      let env, params, defaults, rest = function_params env in
      let returnType = Type.annotation_opt env in
      let env, (_, body, strict) = function_body env ~async ~generator in
      let simple = is_simple_function_params params defaults rest in
      strict_post_check env ~strict ~simple id params;
      let end_loc, expression = Ast.Function.(
        match body with
        | BodyBlock (loc, _) -> loc, false
        | BodyExpression (loc, _) -> loc, true) in
      let loc = Loc.btwn start_loc end_loc in
      env, (loc, Statement.(FunctionDeclaration Function.({
        id;
        params;
        defaults;
        rest;
        body;
        generator;
        async;
        expression;
        returnType;
        typeParameters;
      })))

    let variable_declaration_list : env -> env * Loc.t * Ast.Statement.VariableDeclaration.Declarator.t list * (Loc.t * Error.t) list =
      let variable_declaration env : env * Ast.Statement.VariableDeclaration.Declarator.t * (Loc.t * Error.t) list =
        let env, id = Parse.pattern env Error.StrictVarName in
        let env, init, errs = if Peek.token env = T_ASSIGN
        then begin
          Expect.token env T_ASSIGN;
          let env, expr = Parse.assignment env in
          env, Some expr, []
        end else Ast.Pattern.(
          match id with
          | _, Identifier _ -> env, None, []
          | loc, _ -> env, None, [(loc, Error.NoUninitializedDestructuring)]
        ) in
        let end_loc = match init with
        | Some expr -> fst expr
        | _ -> fst id in
        let declaration = (
          Loc.btwn (fst id) end_loc,
          Ast.Statement.VariableDeclaration.Declarator.({
            id;
            init;
          })
        ) in
        env, declaration, errs

      in let rec helper env decls errs =
        let env, decl, errs_ = variable_declaration env in
        let decls = decl::decls in
        let errs = errs_ @ errs in
        if Peek.token env = T_COMMA
        then begin
          Expect.token env T_COMMA;
          helper env decls errs
        end else
          let end_loc = match decls with
          | (loc, _)::_ -> loc
          | _ -> Loc.none in
          let declarations = List.rev decls in
          let start_loc = match decls with
          | (loc, _)::_ -> loc
          | _ -> Loc.none in
          env, Loc.btwn start_loc end_loc, declarations, List.rev errs

      in fun env -> helper env [] []

    let declarations token kind env : env * (Loc.t * Ast.Statement.VariableDeclaration.t) * (Loc.t * Error.t) list =
      let start_loc = Peek.loc env in
      Expect.token env token;
      let env, loc, declarations, errs = variable_declaration_list env in
      env, (Loc.btwn start_loc loc, Statement.VariableDeclaration.({
        kind;
        declarations;
      })), errs

    let var = declarations T_VAR Statement.VariableDeclaration.Var

    let const env =
      let env = env |> with_no_let true in
      let env, (loc, variable), errs =
        declarations T_CONST Statement.VariableDeclaration.Const env in
      (* Make sure all consts defined are initialized *)
      let errs = Statement.VariableDeclaration.(
        List.fold_left (fun errs decl ->
          match decl with
          | loc, { Declarator.init = None; _ } ->
              (loc, Error.NoUninitializedConst)::errs
          | _ -> errs
        ) errs variable.declarations
      ) in
      env, (loc, variable), List.rev errs

    let _let env : env * (Loc.t * Ast.Statement.VariableDeclaration.t) * (Loc.t * Error.t) list =
      let env = env |> with_no_let true in
      declarations T_LET Statement.VariableDeclaration.Let env

    let variable env : env * Ast.Statement.t * (Loc.t * Error.t) list =
      let start_loc = Peek.loc env in
      let env, (end_loc, variable), errs = match Peek.token env with
      | T_CONST -> const env
      | T_LET   -> _let env
      | T_VAR   -> var env
      | _ ->
          let env = error_unexpected env in
          (* We need to return something. This is as good as anything else *)
          var env in
      let loc = Loc.btwn start_loc end_loc in
      env, (loc, Statement.VariableDeclaration variable), errs
  end

  module Expression = struct
    type op_precedence = Left_assoc of int | Right_assoc of int
    let is_tighter a b =
      let a_prec = match a with Left_assoc x -> x | Right_assoc x -> x - 1 in
      let b_prec = match b with Left_assoc x -> x | Right_assoc x -> x in
      a_prec >= b_prec

    (* AssignmentExpression :
     *   ConditionalExpression
     *   LeftHandSideExpression = AssignmentExpression
     *   LeftHandSideExpression AssignmentOperator AssignmentExpression
     *   ArrowFunctionFunction
     *
     *   Originally we were parsing this without backtracking, but
     *   ArrowFunctionExpression got too tricky. Oh well.
     *)
    let rec assignment : env -> env * Ast.Expression.t =
      let assignment_but_not_arrow_function env : env * Ast.Expression.t =
        let env, expr = conditional env in
        (match assignment_op env with
        | Some operator ->
          let env = if not (is_assignable_lhs expr)
            then error_at env (fst expr, Error.InvalidLHSInAssignment)
            else env in

          let env = match expr with
          | loc, Expression.Identifier (_, { Identifier.name = name; _ })
            when is_restricted name ->
              strict_error_at env (loc, Error.StrictLHSAssignment)
          | _ -> env
          in

          let env, left = Parse.pattern_from_expr env expr in
          let env, right = assignment env in
          let loc = Loc.btwn (fst left) (fst right) in

          let expr = loc, Expression.(Assignment Assignment.({
            operator;
            left;
            right;
          })) in
          env, expr
        | _ -> env, expr)

      in let error_callback _ _ = raise Try.Rollback in

      (* So we may or may not be parsing the first part of an arrow function
       * (the part before the =>). We might end up parsing that whole thing or
       * we might end up parsing only part of it and thinking we're done. We
       * need to look at the next token to figure out if we really parsed an
       * assignment expression or if this is just the beginning of an arrow
       * function *)
      let try_assignment_but_not_arrow_function env : env * Ast.Expression.t =
        let env, prev_callback = env |> with_error_callback error_callback in
        let env, ret = assignment_but_not_arrow_function env in
        let env = env |> restore_error_callback prev_callback in
        match Peek.token env with
        | T_ARROW (* x => 123 *)
        | T_COLON -> (* (x): number => 123 *)
          raise Try.Rollback
        (* async x => 123 -- and we've already parsed async as an identifier
         * expression *)
        | _ when Peek.identifier env -> begin match snd ret with
          | Expression.Identifier (_, {Identifier.name = "async"; _ })
              when not (Peek.line_terminator env) ->
            raise Try.Rollback
          | _ -> env, ret
          end
        | _ -> env, ret

      in fun env ->
        match Peek.token env, Peek.identifier env with
        | T_YIELD, _ when (allow_yield env) -> yield env
        | T_LPAREN, _
        | T_LESS_THAN, _
        | _, true ->

          (* Ok, we don't know if this is going to be an arrow function of a
          * regular assignment expression. Let's first try to parse it as an
          * assignment expression. If that fails we'll try an arrow function.
          *)
          (match Try.to_parse env try_assignment_but_not_arrow_function with
          | Try.ParsedSuccessfully expr -> expr
          | Try.FailedToParse ->
            (match Try.to_parse env try_arrow_function with
              | Try.ParsedSuccessfully expr -> expr
              | Try.FailedToParse ->

                  (* Well shoot. It doesn't parse cleanly as a normal
                   * expression or as an arrow_function. Let's treat it as a
                   * normal assignment expression gone wrong *)
                  assignment_but_not_arrow_function env
            )
          )
        | _ -> assignment_but_not_arrow_function env

    and yield env : env * Ast.Expression.t =
      let start_loc = Peek.loc env in
      Expect.token env T_YIELD;
      let env = if not (allow_yield env)
        then error env Error.IllegalYield
        else env in
      let delegate = Expect.maybe env T_MULT in
      let has_argument = not (
        Peek.token env = T_SEMICOLON || Peek.is_implicit_semicolon env
      ) in
      let argument =
        if delegate || has_argument
        then Some (assignment env)
        else None in
      let env, end_loc, expr = match argument with
      | Some (env, expr) -> env, fst expr, Some expr
      | None ->
          let end_loc = match Peek.semicolon_loc env with
            | Some loc -> loc
            | None -> start_loc in
          let env = Eat.semicolon env in
          env, end_loc, None
      in
      env, (Loc.btwn start_loc end_loc, Expression.(Yield Yield.({
        argument = expr;
        delegate;
      })))

    and is_lhs = Expression.(function
      | _, Member _
      | _, Identifier _ -> true
      | _, Array _
      | _, Object _
      | _, Literal _
      | _, TemplateLiteral _
      | _, TaggedTemplate _
      | _, This
      | _, Class _
      | _, Function _
      | _, New _
      | _, Call _
      | _, Comprehension _
      | _, Generator _
      | _, Assignment _
      | _, Binary _
      | _, Conditional _
      | _, Logical _
      | _, Sequence _
      | _, Unary _
      | _, Update _
      | _, ArrowFunction _
      | _, Yield _
      | _, JSXElement _
      | _, Let _
      | _, TypeCast _ -> false)

    and is_assignable_lhs = Expression.(function
      | _, Array _
      | _, Object _
      | _, Member _
      | _, Identifier _ -> true
      | _, Literal _
      | _, TemplateLiteral _
      | _, TaggedTemplate _
      | _, This
      | _, Class _
      | _, Function _
      | _, New _
      | _, Call _
      | _, Comprehension _
      | _, Generator _
      | _, Assignment _
      | _, Binary _
      | _, Conditional _
      | _, Logical _
      | _, Sequence _
      | _, Unary _
      | _, Update _
      | _, ArrowFunction _
      | _, Yield _
      | _, JSXElement _
      | _, Let _
      | _, TypeCast _ -> false)


    and assignment_op env =
      let op = Expression.Assignment.(match Peek.token env with
      | T_RSHIFT3_ASSIGN -> Some RShift3Assign
      | T_RSHIFT_ASSIGN -> Some RShiftAssign
      | T_LSHIFT_ASSIGN -> Some LShiftAssign
      | T_BIT_XOR_ASSIGN -> Some BitXorAssign
      | T_BIT_OR_ASSIGN -> Some BitOrAssign
      | T_BIT_AND_ASSIGN -> Some BitAndAssign
      | T_MOD_ASSIGN -> Some ModAssign
      | T_DIV_ASSIGN -> Some DivAssign
      | T_MULT_ASSIGN -> Some MultAssign
      | T_EXP_ASSIGN -> Some ExpAssign
      | T_MINUS_ASSIGN -> Some MinusAssign
      | T_PLUS_ASSIGN -> Some PlusAssign
      | T_ASSIGN -> Some Assign
      | _ -> None) in
      if op <> None then Eat.token env;
      op

    and conditional env : env * Ast.Expression.t =
      let start_loc = Peek.loc env in
      let expr = logical env in
      if Peek.token env = T_PLING
      then begin
        Expect.token env T_PLING;
        (* no_in is ignored for the consequent *)
        let env' = env |> with_no_in false in
        let env, consequent = assignment env' in
        Expect.token env T_COLON;
        let env, end_loc, alternate = with_loc assignment env in
        let loc = Loc.btwn start_loc end_loc in
        let expr = loc, Expression.(Conditional Conditional.({
          test = expr;
          consequent;
          alternate;
        })) in
        env, expr
      end else env, expr

    and logical =
      let open Expression in
      let make_logical left right operator loc =
        loc, Logical Logical.({operator; left; right;})
      in let rec logical_and env left lloc =
        match Peek.token env with
        | T_AND ->
            Expect.token env T_AND;
            let env, rloc, right = with_loc binary env in
            let loc = Loc.btwn lloc rloc in
            logical_and env (make_logical left right Logical.And loc) loc
        | _  -> lloc, left
      and logical_or env left lloc =
        match Peek.token env with
        | T_OR ->
            Expect.token env T_OR;
            let env, rloc, right = with_loc binary env in
            let rloc, right = logical_and env right rloc in
            let loc = Loc.btwn lloc rloc in
            logical_or env (make_logical left right Logical.Or loc) loc
        | _ -> lloc, left
      in fun env ->
        let env, loc, left = with_loc binary env in
        let loc, left = logical_and env left loc in
        let _, type_ = logical_or env left loc in
        type_

    and binary : env -> env * Ast.Expression.t =
      let binary_op env =
        let ret = Expression.Binary.(match Peek.token env with
        (* Most BinaryExpression operators are left associative *)
        (* Lowest pri *)
        | T_BIT_OR -> Some (BitOr, Left_assoc 2)
        | T_BIT_XOR -> Some (Xor, Left_assoc 3)
        | T_BIT_AND -> Some (BitAnd, Left_assoc 4)
        | T_EQUAL -> Some (Equal, Left_assoc 5)
        | T_STRICT_EQUAL -> Some (StrictEqual, Left_assoc 5)
        | T_NOT_EQUAL -> Some (NotEqual, Left_assoc 5)
        | T_STRICT_NOT_EQUAL -> Some (StrictNotEqual, Left_assoc 5)
        | T_LESS_THAN -> Some (LessThan, Left_assoc 6)
        | T_LESS_THAN_EQUAL -> Some (LessThanEqual, Left_assoc 6)
        | T_GREATER_THAN -> Some (GreaterThan, Left_assoc 6)
        | T_GREATER_THAN_EQUAL -> Some (GreaterThanEqual, Left_assoc 6)
        | T_IN ->
            if (no_in env) then None else Some (In, Left_assoc 6)
        | T_INSTANCEOF -> Some (Instanceof, Left_assoc 6)
        | T_LSHIFT -> Some (LShift, Left_assoc 7)
        | T_RSHIFT -> Some (RShift, Left_assoc 7)
        | T_RSHIFT3 -> Some (RShift3, Left_assoc 7)
        | T_PLUS -> Some (Plus, Left_assoc 8)
        | T_MINUS -> Some (Minus, Left_assoc 8)
        | T_MULT -> Some (Mult, Left_assoc 9)
        | T_DIV -> Some (Div, Left_assoc 9)
        | T_MOD -> Some (Mod, Left_assoc 9)
        | T_EXP -> Some (Exp, Right_assoc 10)
        (* Highest priority *)
        | _ -> None)
        in if ret <> None then Eat.token env;
        ret

      in let make_binary left right operator loc =
        loc, Expression.(Binary Binary.({
          operator;
          left;
          right;
        }))

      in let rec add_to_stack right (rop, rpri) rloc = function
        | (left, (lop, lpri), lloc)::rest when is_tighter lpri rpri ->
            let loc = Loc.btwn lloc rloc in
            let right = make_binary left right lop loc in
            add_to_stack right (rop, rpri) loc rest
        | stack -> (right, (rop, rpri), rloc)::stack

      in let rec collapse_stack right rloc = function
        | [] -> right
        | (left, (lop, _), lloc)::rest ->
            let loc = Loc.btwn lloc rloc in
            collapse_stack (make_binary left right lop loc) loc rest

      in let rec helper env stack =
        let start_loc = Peek.loc env in
        let is_unary = peek_unary_op env <> None in
        let prev_no_in = no_in env in
        let env = env |> with_no_in false in
        let env, right = unary env in
        let env = env |> with_no_in prev_no_in in
        let end_loc = match last_loc env with
        | Some loc -> loc
        | None -> fst right
        in
        let right_loc = Loc.btwn start_loc end_loc in
        let env =
          if Peek.token env = T_LESS_THAN
          then
            match right with
            | _, Expression.JSXElement _ ->
                error env Error.AdjacentJSXElements
            | _ -> env
          else env
        in
        match binary_op env with
        | None ->
          env, collapse_stack right right_loc stack
        | Some (rop, rpri) ->
          let env = if is_unary && rop = Expression.Binary.Exp
            then error_at env (right_loc, Error.InvalidLHSInExponentiation)
            else env in
          helper env (add_to_stack right (rop, rpri) right_loc stack)

      in fun env -> helper env []

    and peek_unary_op env =
      let open Expression.Unary in
      match Peek.token env with
      | T_NOT -> Some Not
      | T_BIT_NOT -> Some BitNot
      | T_PLUS -> Some Plus
      | T_MINUS -> Some Minus
      | T_TYPEOF -> Some Typeof
      | T_VOID -> Some Void
      | T_DELETE -> Some Delete
      (* If we are in a unary expression context, and within an async function,
       * assume that a use of "await" is intended as a keyword, not an ordinary
       * identifier. This is a little bit inconsistent, since it can be used as
       * an identifier in other contexts (such as a variable name), but it's how
       * Babel does it. *)
      | T_AWAIT when allow_await env -> Some Await
      | _ -> None

    and unary env : env * Ast.Expression.t =
      let begin_loc = Peek.loc env in
      let op = peek_unary_op env in
      match op with
      | None -> begin
          let op = Expression.Update.(match Peek.token env with
          | T_INCR -> Some Increment
          | T_DECR -> Some Decrement
          | _ -> None) in
          match op with
          | None -> env, postfix env
          | Some operator ->
              Eat.token env;
              let env, argument = unary env in
              let env = if not (is_lhs argument)
                then error_at env (fst argument, Error.InvalidLHSInAssignment)
                else env in
              let env = match argument with
              | _, Expression.Identifier (_, { Identifier.name; _ })
                when is_restricted name ->
                  strict_error env Error.StrictLHSPrefix
              | _ -> env
              in
              let loc = Loc.btwn begin_loc (fst argument) in
              let expr = loc, Expression.(Update Update.({
                operator;
                prefix = true;
                argument;
              })) in
              env, expr
        end
      | Some operator ->
        Eat.token env;
        let env, argument = unary env in
        let loc = Loc.btwn begin_loc (fst argument) in
        let env = Expression.(match operator, argument with
        | Unary.Delete, (_, Identifier _) ->
            strict_error_at env (loc, Error.StrictDelete)
        | _ -> env)
        in
        let expr = loc, Expression.(Unary Unary.({
          operator;
          prefix = true;
          argument;
        })) in
        env, expr

    and postfix env =
      let env, argument = left_hand_side env in
      (* No line terminator allowed before operator *)
      if Peek.line_terminator env
      then argument
      else let op = Expression.Update.(match Peek.token env with
      | T_INCR -> Some Increment
      | T_DECR -> Some Decrement
      | _ -> None) in
      match op with
      | None -> argument
      | Some operator ->
          let env = if not (is_lhs argument)
            then error_at env (fst argument, Error.InvalidLHSInAssignment)
            else env in
          let env = match argument with
          | _, Expression.Identifier (_, { Identifier.name; _ })
            when is_restricted name ->
              strict_error env Error.StrictLHSPostfix
          | _ -> env
          in
          let end_loc = Peek.loc env in
          Eat.token env;
          Loc.btwn (fst argument) end_loc, Expression.(Update Update.({
            operator;
            prefix = false;
            argument;
          }))

    and left_hand_side env : env * Ast.Expression.t =
      let env, expr = match Peek.token env with
      | T_NEW -> _new env (fun new_expr _args -> new_expr)
      | _ when Peek._function env -> _function env
      | _ -> primary env in
      let env, expr = member env expr in
      match Peek.token env with
      | T_LPAREN ->
          call env expr
      | T_TEMPLATE_PART part ->
          let env, expr = tagged_template env expr part in
          member env expr
      | _ -> env, expr

    and call env (left: Ast.Expression.t) : env * Ast.Expression.t =
      match Peek.token env with
      | T_LPAREN when not (no_call env) ->
          let env, (args_loc, args) = arguments env in
          call env (Loc.btwn (fst left) args_loc, Expression.(Call Call.({
            callee = left;
            arguments = args;
          })))
      | T_LBRACKET ->
          Expect.token env T_LBRACKET;
          let env, expr = Parse.expression env in
          let last_loc = Peek.loc env in
          let loc = Loc.btwn (fst left) last_loc in
          Expect.token env T_RBRACKET;
          call env (loc, Expression.(Member Member.({
            _object  = left;
            property = PropertyExpression expr;
            computed = true;
          })))
      | T_PERIOD ->
          Expect.token env T_PERIOD;
          let env, id, _ = identifier_or_reserved_keyword env in
          call env (Loc.btwn (fst left) (fst id), Expression.(Member Member.({
            _object  = left;
            property = PropertyIdentifier id;
            computed = false;
          })))
      | T_TEMPLATE_PART part -> tagged_template env left part
      | _ -> env, left

    and _new env (finish_fn: Ast.Expression.t -> (Loc.t * Ast.Expression.expression_or_spread list) option -> Ast.Expression.t): env * Ast.Expression.t =
      match Peek.token env with
      | T_NEW ->
          let start_loc = Peek.loc env in
          Expect.token env T_NEW;
          let finish_fn' callee args =
            let end_loc, arguments = match args with
            | Some (loc, args) -> loc, args
            | _ -> fst callee, [] in
            let callee' = Loc.btwn start_loc end_loc, Expression.(New New.({
              callee;
              arguments;
            })) in
            finish_fn callee' None in
          _new env finish_fn'
      | _ ->
          let env, expr = match Peek.token env with
          | _ when Peek._function env -> _function env
          | _ -> primary env in
          let prev_no_call = no_call env in
          let env = env |> with_no_call true in
          let env, callee = member env expr in
          let env = env |> with_no_call prev_no_call in
          (* You can do something like
           *   new raw`42`
           *)
          let env, callee = match Peek.token env with
          | T_TEMPLATE_PART part -> tagged_template env callee part
          | _ -> env, callee in
          let env, args = match Peek.token env with
          | T_LPAREN -> let env, args = arguments env in env, Some args
          | _ -> env, None in
          env, finish_fn callee args

    and arguments : env -> env * (Loc.t * Ast.Expression.expression_or_spread list) =
      let argument env : env * Ast.Expression.expression_or_spread =
        match Peek.token env with
        | T_ELLIPSIS ->
            let start_loc = Peek.loc env in
            Expect.token env T_ELLIPSIS;
            let env, argument = assignment env in
            let loc = Loc.btwn start_loc (fst argument) in
            env, Expression.(Spread (loc, SpreadElement.({
              argument;
            })))
        | _ ->
            let env, expr = assignment env in
            env, Expression.Expression expr

      in let rec arguments' env acc =
        match Peek.token env with
        | T_EOF
        | T_RPAREN -> env, List.rev acc
        | _ ->
            let env, arg = argument env in
            let acc = arg::acc in
            if Peek.token env <> T_RPAREN
            then Expect.token env T_COMMA;
            arguments' env acc

      in fun env ->
        let start_loc = Peek.loc env in
        Expect.token env T_LPAREN;

        let env, args = arguments' env []

        in let end_loc = Peek.loc env in
        Expect.token env T_RPAREN;
        env, (Loc.btwn start_loc end_loc, args)

    and member env (left: Ast.Expression.t) : env * Ast.Expression.t =
      match Peek.token env with
      | T_LBRACKET ->
          Expect.token env T_LBRACKET;
          let prev_no_call = no_call env in
          let env = env |> with_no_call false in
          let env, expr = Parse.expression env in
          let env = env |> with_no_call prev_no_call in
          let last_loc = Peek.loc env in
          Expect.token env T_RBRACKET;
          call env (Loc.btwn (fst left) last_loc, Expression.(Member Member.({
            _object  = left;
            property = PropertyExpression expr;
            computed = true;
          })))
      | T_PERIOD ->
          Expect.token env T_PERIOD;
          let env, id, _ = identifier_or_reserved_keyword env in
          call env (Loc.btwn (fst left) (fst id), Expression.(Member Member.({
            _object  = left;
            property = PropertyIdentifier id;
            computed = false;
          })))
      | _ -> env, left

    and _function env : env * Ast.Expression.t =
      let start_loc = Peek.loc env in
      let async = Declaration.async env in
      Expect.token env T_FUNCTION;
      let env, generator = Declaration.generator env async in
      let env, id, typeParameters =
        if Peek.token env = T_LPAREN
        then env, None, None
        else begin
          let env, id = match Peek.token env with
            | T_LESS_THAN -> env, None
            | _ ->
              let env, id =
                Parse.identifier ~restricted_error:Error.StrictFunctionName env
              in
              env, Some id
          in
          env, id, Type.type_parameter_declaration env
        end in
      let env, params, defaults, rest = Declaration.function_params env in
      let returnType = Type.annotation_opt env in
      let env, (end_loc, body, strict) =
        Declaration.function_body env ~async ~generator in
      let simple = Declaration.is_simple_function_params params defaults rest in
      Declaration.strict_post_check env ~strict ~simple id params;
      let expression = Function.(
        match body with
        | BodyBlock _ -> false
        | BodyExpression _ -> true) in
      env, (Loc.btwn start_loc end_loc, Expression.(Function Function.({
        id;
        params;
        defaults;
        rest;
        body;
        generator;
        async;
        expression;
        returnType;
        typeParameters;
      })))

    and number env (number_type: number_type) : env * float =
      let value = Peek.value env in
      let env, value = match number_type with
      | LEGACY_OCTAL ->
        strict_error env Error.StrictOctalLiteral,
        float (int_of_string ("0o"^value))
      | BINARY
      | OCTAL ->
        env, float (int_of_string value)
      | NORMAL ->
        env, float_of_string value
      in
      Expect.token env (T_NUMBER number_type);
      env, value

    and primary env : env * Ast.Expression.t =
      let loc = Peek.loc env in
      match Peek.token env with
      | T_THIS ->
          Expect.token env T_THIS;
          env, (loc, Expression.This)
      | T_NUMBER number_type ->
          let raw = Peek.value env in
          let env, num = number env number_type in
          let value = Literal.Number num in
          env, (loc, Expression.(Literal { Literal.value; raw; }))
      | T_STRING (loc, value, raw, octal) ->
          let env = if octal
            then strict_error env Error.StrictOctalLiteral
            else env in
          Expect.token env (T_STRING (loc, value, raw, octal));
          let value = Literal.String value in
          env, (loc, Expression.(Literal { Literal.value; raw; }))
      | (T_TRUE | T_FALSE) as token ->
          let raw = Peek.value env in
          Expect.token env token;
          let value = (Literal.Boolean (token = T_TRUE)) in
          env, (loc, Expression.(Literal { Literal.value; raw; }))
      | T_NULL ->
          let raw = Peek.value env in
          Expect.token env T_NULL;
          let value = Literal.Null in
          env, (loc, Expression.(Literal { Literal.value; raw; }))
      | T_LPAREN -> group env
      | T_LCURLY -> object_initializer env
      | T_LBRACKET ->
          let env, (loc, arr) = array_initializer env in
          env, (loc, Expression.Array arr)
      | T_DIV
      | T_DIV_ASSIGN -> regexp env
      | T_LESS_THAN ->
          let env, (loc, element) = Parse.jsx_element env in
          env, (loc, Expression.JSXElement element)
      | T_TEMPLATE_PART part ->
          let env, (loc, template) = template_literal env part in
          env, (loc, Expression.(TemplateLiteral template))
      | T_CLASS -> Parse.class_expression env
      | T_SUPER ->
          let loc = Peek.loc env in
          Expect.token env T_SUPER;
          let id = loc, {
            Identifier.name = "super";
            typeAnnotation = None;
            optional = false; } in
          env, (loc, Expression.Identifier id)
      | _ when Peek.identifier env ->
          let env, id = Parse.identifier env in
          env, (fst id, Expression.Identifier id)
      | t ->
          let env = error_unexpected env in
          (* Let's get rid of the bad token *)
          if t = T_ERROR
          then Eat.token env;
          (* Really no idea how to recover from this. I suppose a null
           * expression is as good as anything *)
          let value = Literal.Null in
          let raw = "null" in
          env, (loc, Expression.(Literal { Literal.value; raw; }))

    and object_initializer env : env * Ast.Expression.t =
      let env, (loc, obj) = Parse.object_initializer env in
      env, (loc, Expression.Object obj)

    and template_literal :
        env ->
        Ast.Expression.TemplateLiteral.Element.t * string ->
        env * Ast.Expression.TemplateLiteral.t =
      let rec template_parts env quasis expressions =
        let env, expr = Parse.expression env in
        let expressions = expr::expressions in
        match Peek.token env with
        | T_RCURLY ->
            let lex_env, lex_result = lex_template_tail (lex_env env) in
            set_lex_env env lex_env;
            Eat.advance env (lex_env, lex_result);
            let loc, part = match lex_result.lex_token with
            | T_TEMPLATE_PART ((loc, part), _) -> loc, part
            | _ -> assert false in
            let quasis = (loc, part)::quasis in
            if part.Expression.TemplateLiteral.Element.tail
            then env, loc, List.rev quasis, List.rev expressions
            else template_parts env quasis expressions
        | _ ->
            (* Malformed template *)
            let env = error_unexpected env in
            let loc = fst expr in
            let imaginary_quasi = loc, Expression.TemplateLiteral.Element.({
              value = {
                raw = "";
                cooked = "";
              };
              tail = true;
            }) in
            env, loc, List.rev (imaginary_quasi::quasis), List.rev expressions

      in fun env ((head, _) as part) ->
        Expect.token env (T_TEMPLATE_PART part);
        let start_loc = fst head in
        let env, end_loc, quasis, expressions =
          if (snd head).Expression.TemplateLiteral.Element.tail
          then env, start_loc, [head], []
          else template_parts env [head] [] in
        let loc = Loc.btwn start_loc end_loc in
        let expr = loc, Expression.TemplateLiteral.({
          quasis;
          expressions;
        }) in
        env, expr

    and tagged_template
        (env: env)
        (tag: Ast.Expression.t)
        (part: Ast.Expression.TemplateLiteral.Element.t * string)
        : env * Ast.Expression.t =
      let env, quasi = template_literal env part in
      let loc = Loc.btwn (fst tag) (fst quasi) in
      let expr = loc, Expression.(TaggedTemplate TaggedTemplate.({
        tag;
        quasi;
      })) in
      env, expr

    and group env : env * Ast.Expression.t =
      Expect.token env T_LPAREN;
      let env, expression = assignment env in
      let env, ret = (match Peek.token env with
      | T_COMMA -> sequence env [expression]
      | T_COLON ->
          let typeAnnotation = Type.annotation env in
          let loc = Loc.btwn (fst expression) (fst typeAnnotation) in
          let expr = Expression.(loc,
            TypeCast TypeCast.({
              expression;
              typeAnnotation;
            }))
          in
          env, expr
      | _ -> env, expression) in
      Expect.token env T_RPAREN;
      env, ret

    and array_initializer : env -> env * Ast.Expression.Array.t =
      let rec elements env acc =
        match Peek.token env with
        | T_EOF
        | T_RBRACKET -> List.rev acc
        | T_COMMA ->
            Expect.token env T_COMMA;
            elements env (None::acc)
        | T_ELLIPSIS ->
            let start_loc = Peek.loc env in
            Expect.token env T_ELLIPSIS;
            let env, argument = assignment env in
            let loc = Loc.btwn start_loc (fst argument) in
            let elem = Expression.(Spread (loc, SpreadElement.({
              argument;
            }))) in
            elements env ((Some elem)::acc)
        | _ ->
            let env, expr = assignment env in
            let elem = Expression.Expression expr in
            if Peek.token env <> T_RBRACKET then Expect.token env T_COMMA;
            elements env ((Some elem)::acc)

      in fun env ->
        let start_loc = Peek.loc env in
        Expect.token env T_LBRACKET;
        let elements = elements env [] in
        let end_loc = Peek.loc env in
        Expect.token env T_RBRACKET;
        let arr = Loc.btwn start_loc end_loc, Expression.Array.({
          elements;
        }) in
        env, arr

    and regexp env : env * Ast.Expression.t =
      let lex_env, lex_result = lex_regexp (lex_env env) in
      set_lex_env env lex_env;
      Eat.advance env (lex_env, lex_result);
      let pattern, raw_flags = match lex_result.lex_token with
        | T_REGEXP (_, pattern, flags) -> pattern, flags
        | _ -> assert false in
      let filtered_flags = Buffer.create (String.length raw_flags) in
      String.iter (function
        | 'g' | 'i' | 'm' | 'y' as c -> Buffer.add_char filtered_flags c
        | _ -> ()) raw_flags;
      let flags = Buffer.contents filtered_flags in
      let env = if flags <> raw_flags
        then error env (Error.InvalidRegExpFlags raw_flags)
        else env in
      let value = Literal.(RegExp { RegExp.pattern; flags; }) in
      let raw = lex_result.lex_value in
      env, (lex_result.lex_loc, Expression.(Literal { Literal.value; raw; }))

    and try_arrow_function : env -> env * Ast.Expression.t =
      (* Certain errors (almost all errors) cause a rollback *)
      let error_callback _ = Error.(function
        (* Don't rollback on these errors. *)
        | StrictParamName
        | ParameterAfterRestParameter
        | NewlineBeforeArrow -> ()
        (* Everything else causes a rollback *)
        | _ -> raise Try.Rollback) in

      fun env ->
        let env, prev_callback = env |> with_error_callback error_callback in

        let start_loc = Peek.loc env in
        (* a T_ASYNC could either be a parameter name or it could be indicating
         * that it's an async function *)
        let async = Peek.token ~i:1 env <> T_ARROW && Declaration.async env in
        let typeParameters = Type.type_parameter_declaration env in
        let env, params, defaults, rest, returnType =
          (* Disallow all fancy features for identifier => body *)
          if Peek.identifier env && typeParameters = None
          then
            let env, id =
              Parse.identifier ~restricted_error:Error.StrictParamName env in
            let param = fst id, Pattern.Identifier id in
            env, [param], [], None, None
          else
            let env, params, defaults, rest = Declaration.function_params env in
            env, params, defaults, rest, Type.annotation_opt env in

        (* It's hard to tell if an invalid expression was intended to be an
         * arrow function before we see the =>. If there are no params, that
         * implies "()" which is only ever found in arrow params. Similarly,
         * rest params indicate arrow functions. Therefore, if we see a rest
         * param or an empty param list then we can disable the rollback and
         * instead generate errors as if we were parsing an arrow function *)
        let env =
          if params = [] || rest <> None
          then fst (without_error_callback env)
          else env in

        let env = if Peek.line_terminator env && Peek.token env = T_ARROW
          then error env Error.NewlineBeforeArrow
          else env in
        Expect.token env T_ARROW;

        (* Now we know for sure this is an arrow function *)
        let env, _ = without_error_callback env in

        let env, end_loc, (body, strict) = with_loc
          (Declaration.concise_function_body ~async ~generator:false)
          env
        in
        let simple =
          Declaration.is_simple_function_params params defaults rest in
        Declaration.strict_post_check env ~strict ~simple None params;
        let expression = Function.(
          match body with
          | BodyBlock _ -> false
          | BodyExpression _ -> true) in
        let loc = Loc.btwn start_loc end_loc in
        let expr = loc, Expression.(ArrowFunction Function.({
          id = None;
          params;
          defaults;
          rest;
          body;
          async;
          generator = false; (* arrow functions cannot be generators *)
          expression;
          returnType;
          typeParameters;
        })) in
        let env = restore_error_callback prev_callback env in
        env, expr

    and sequence env acc : env * Ast.Expression.t =
      match Peek.token env with
      | T_COMMA ->
          Expect.token env T_COMMA;
          let env, expr = assignment env in
          sequence env (expr::acc)
      | _ ->
        let last_loc = (match acc with
          | (loc, _)::_ -> loc
          | _ -> Loc.none) in
        let expressions = List.rev acc in
        let first_loc = (match expressions with
          | (loc, _)::_ -> loc
          | _ -> Loc.none) in
        let expr = Loc.btwn first_loc last_loc, Expression.(Sequence Sequence.({
          expressions;
        })) in
        env, expr

    (* You can do things like
     * var x = { if : 4 }
     * x.if
     *)
    and identifier_or_reserved_keyword env =
      let { lex_token; lex_value; lex_loc; _ } = lookahead env in
      match lex_token with
      | T_IDENTIFIER ->
        let env, id = Parse.identifier env in
        env, id, None
      | _ ->
        let env, err = match lex_token with
        | T_FUNCTION
        | T_IF
        | T_IN
        | T_INSTANCEOF
        | T_RETURN
        | T_SWITCH
        | T_THIS
        | T_THROW
        | T_TRY
        | T_VAR
        | T_WHILE
        | T_WITH
        | T_CONST
        | T_LET
        | T_NULL
        | T_FALSE
        | T_TRUE
        | T_BREAK
        | T_CASE
        | T_CATCH
        | T_CONTINUE
        | T_DECLARE
        | T_DEFAULT
        | T_DO
        | T_FINALLY
        | T_FOR
        | T_CLASS
        | T_EXTENDS
        | T_STATIC
        | T_ELSE
        | T_NEW
        | T_DELETE
        | T_TYPEOF
        | T_VOID
        | T_ENUM
        | T_EXPORT
        | T_IMPORT
        | T_SUPER
        | T_IMPLEMENTS
        | T_INTERFACE
        | T_PACKAGE
        | T_PRIVATE
        | T_PROTECTED
        | T_PUBLIC
        | T_YIELD
        | T_TYPE
        | T_OF
        | T_ANY_TYPE
        | T_BOOLEAN_TYPE
        | T_NUMBER_TYPE
        | T_STRING_TYPE
        | T_VOID_TYPE
        | T_ASYNC
        | T_AWAIT
        | T_DEBUGGER ->
            env, Some (lex_loc, get_unexpected_error (lex_token, lex_value))
        | _ ->
            let env = error_unexpected env in
            env, None
        in
        Eat.token env;
        env, (lex_loc, Identifier.({
          name = lex_value;
          typeAnnotation = None;
          optional = false;
        })), err
  end

  (* A module for parsing various object related things, like object literals
   * and classes *)
  module Object : sig
    val key : env -> env * (Loc.t * Ast.Expression.Object.Property.key)
    val _initializer : env -> env * Ast.Expression.Object.t
    val class_declaration : env -> Ast.Expression.t list -> env * Ast.Statement.t
    val class_expression : env -> env * Ast.Expression.t
    val decorator_list : env -> Ast.Expression.t list
  end = struct
    let decorator_list =
      let rec decorator_list_helper env decorators =
        match Peek.token env with
        | T_AT ->
            Eat.token env;
            let env, lhs = Expression.left_hand_side env in
            decorator_list_helper env (lhs::decorators)
        | _ ->
            decorators

      in fun env ->
        if (parse_options env).esproposal_decorators
        then List.rev (decorator_list_helper env [])
        else []

    let key ?allow_computed_key:(allow_computed_key=true) env =
      Ast.Expression.Object.Property.(match Peek.token env with
      | T_STRING (loc, value, raw, octal) ->
          let env = if octal
            then strict_error env Error.StrictOctalLiteral
            else env in
          Expect.token env (T_STRING (loc, value, raw, octal));
          let value = Literal.String value in
          env, (loc, Literal (loc, { Literal.value; raw; }))
      | T_NUMBER number_type ->
          let raw = Peek.value env in
          let loc = Peek.loc env in
          let env, value = Expression.number env number_type in
          let value = Literal.Number value in
          env, (loc,  Literal (loc, { Literal.value; raw; }))
      | T_LBRACKET when allow_computed_key ->
          let start_loc = Peek.loc env in
          Expect.token env T_LBRACKET;
          let env, expr = Parse.assignment (env |> with_no_in false) in
          let end_loc = Peek.loc env in
          Expect.token env T_RBRACKET;
          let loc = Loc.btwn start_loc end_loc in
          env, (loc, Ast.Expression.Object.Property.Computed expr)
      | _ ->
          let env, id, _ = Expression.identifier_or_reserved_keyword env in
          env, (fst id, Identifier id))

    let _method env kind =
      (* this is a getter or setter, it cannot be async *)
      let async = false in
      let env, generator = Declaration.generator env async in
      let env, (_, key) = key env in
      (* It's not clear how type params on getters & setters would make sense
       * in Flow's type system. Since this is a Flow syntax extension, we might
       * as well disallow it until we need it *)
      let typeParameters = Ast.Expression.Object.Property.(match kind with
      | Get | Set -> None
      | _ -> Type.type_parameter_declaration env) in
      Expect.token env T_LPAREN;
      let env, params = Ast.Expression.Object.Property.(match kind with
      | Get -> env, []
      | Set ->
        (* TODO: support more param pattern types here *)
        let env, param = Parse.identifier_with_type env Error.StrictParamName in
        env, [ (fst param, Pattern.Identifier param) ]
      | Init -> assert false) in
      Expect.token env T_RPAREN;
      let returnType = Type.annotation_opt env in
      let env, (_, body, strict) =
        Declaration.function_body env ~async ~generator in
      let defaults = [] in
      let rest = None in
      let simple = Declaration.is_simple_function_params params defaults rest in
      Declaration.strict_post_check env ~strict ~simple None params;
      let end_loc, expression = Function.(
        match body with
        | BodyBlock (loc, _) -> loc, false
        | BodyExpression (loc, _) -> loc, true) in
      let value = end_loc, Function.({
        id = None;
        params;
        defaults;
        rest;
        body;
        generator;
        async;
        expression;
        returnType;
        typeParameters;
      }) in
      key, value

    let _initializer : env -> env * Ast.Expression.Object.t =
      let rec property env = Ast.Expression.Object.(
        let start_loc = Peek.loc env in
        if Peek.token env = T_ELLIPSIS
        then begin
          (* Spread property *)
          Expect.token env T_ELLIPSIS;
          let env, argument = Parse.assignment env in
          let loc = Loc.btwn start_loc (fst argument) in
          env, SpreadProperty (loc, SpreadProperty.({ argument; }))
        end else begin
          (* look for a following identifier to tell whether to parse a function
           * or not *)
          let async = Peek.identifier ~i:1 env && Declaration.async env in
          let env, generator = Declaration.generator env async in
          let env, obj_key = key env in
          let env, prop = match async, generator, obj_key with
          | false, false, (_, (Property.Identifier (_, { Ast.Identifier.name =
              "get"; _}) as key)) ->
              (match Peek.token env with
              | T_COLON
              | T_LESS_THAN
              | T_LPAREN -> init env start_loc key false false
              | _ -> get env start_loc)
          | false, false, (_, (Property.Identifier (_, { Ast.Identifier.name =
              "set"; _}) as key)) ->
              (match Peek.token env with
              | T_COLON
              | T_LESS_THAN
              | T_LPAREN -> init env start_loc key false false
              | _ -> set env start_loc)
          | async, generator, (_, key) ->
              init env start_loc key async generator
          in
          env, Property prop
        end
      )

      and get env start_loc =
        let key, (end_loc, fn) =
          _method env Ast.Expression.Object.Property.Get in
        let value = end_loc, Ast.Expression.Function fn in
        let loc = Loc.btwn start_loc end_loc in
        env, (loc, Ast.Expression.Object.Property.({
          key;
          value;
          kind = Get;
          _method = false;
          shorthand = false;
        }))

      and set env start_loc =
        let key, (end_loc, fn) =
          _method env Ast.Expression.Object.Property.Set in
        let value = end_loc, Ast.Expression.Function fn in
        let loc = Loc.btwn start_loc end_loc in
        env, (loc, Ast.Expression.Object.Property.({
          key;
          value;
          kind = Set;
          _method = false;
          shorthand = false;
        }))

      and init env start_loc key async generator =
        Ast.Expression.Object.Property.(
          let env, value, shorthand, _method =
            match Peek.token env with
            | T_RCURLY
            | T_COMMA ->
                let value = match key with
                | Literal lit -> fst lit, Ast.Expression.Literal (snd lit)
                | Identifier id -> fst id, Ast.Expression.Identifier id
                | Computed expr -> expr
                in
                env, value, true, false
            | T_LESS_THAN
            | T_LPAREN ->
                let typeParameters = Type.type_parameter_declaration env in
                let env, params, defaults, rest = Declaration.function_params env in
                let returnType = Type.annotation_opt env in
                let env, (_, body, strict) =
                  Declaration.function_body env ~async ~generator in
                let simple = Declaration.is_simple_function_params params defaults rest in
                Declaration.strict_post_check env ~strict ~simple None params;
                let end_loc, expression = Function.(
                  match body with
                  | BodyBlock (loc, _) -> loc, false
                  | BodyExpression (loc, _) -> loc, true) in
                let value = end_loc, Ast.Expression.(Function Function.({
                  id = None;
                  params;
                  defaults;
                  rest;
                  body;
                  generator;
                  async;
                  expression;
                  returnType;
                  typeParameters;
                })) in
                env, value, false, true
            | _ ->
              Expect.token env T_COLON;
              let env, value = Parse.assignment env in
              env, value, false, false
          in
          let loc = Loc.btwn start_loc (fst value) in
          env, (loc, {
            key;
            value;
            kind = Init;
            _method;
            shorthand;
          })
        )

      and check_property env prop_map prop = Ast.Expression.Object.(
        match prop with
        | Property (prop_loc, ({ Property.key = Property.Literal _ | Property.Identifier _; _ } as prop)) ->
            Property.(
              let key = match prop.key with
              | Literal (_, { Literal.value = Literal.String s; _; } ) -> s
              | Literal (_, { Literal.value = Literal.Boolean b; _; } ) -> string_of_bool b
              | Literal (_, { Literal.value = Literal.Null; _; } ) -> "null"
              | Literal (_, { Literal.value = Literal.Number f; _; } ) -> string_of_float f
              | Literal (_, { Literal.value = Literal.RegExp _; _; } ) ->
                  failwith "RegExp cannot be property key"
              | Identifier (_, { Identifier.name; _ }) -> name
              | Computed _ -> assert false in
              let prev_kinds =
                try SMap.find key prop_map
                with Not_found -> SSet.empty in
              let kind_string = match prop.kind with
              | Init -> "Init"
              | Get -> "Get"
              | Set -> "Set" in
              let env = match kind_string with
              | "Init" when SSet.mem "Init" prev_kinds ->
                  strict_error_at env (prop_loc, Error.StrictDuplicateProperty)
              | "Init" when SSet.mem "Set" prev_kinds || SSet.mem "Get" prev_kinds ->
                  error_at env (prop_loc, Error.AccessorDataProperty)
              | "Get"
              | "Set" when SSet.mem "Init" prev_kinds ->
                  error_at env (prop_loc, Error.AccessorDataProperty)
              | ("Get" | "Set") as kind when SSet.mem kind prev_kinds ->
                  error_at env (prop_loc, Error.AccessorGetSet)
              | _ -> env
              in
              let kinds = SSet.add kind_string prev_kinds in
              env, SMap.add key kinds prop_map)
        | _ -> env, prop_map
      )

      and properties env (prop_map, acc) =
        match Peek.token env with
        | T_EOF
        | T_RCURLY -> List.rev acc
        | _ ->
            let env, prop = property env in
            let env, prop_map = check_property env prop_map prop in
            if Peek.token env <> T_RCURLY then Expect.token env T_COMMA;
            properties env (prop_map, prop::acc)

      in fun env ->
        let start_loc = Peek.loc env in
        Expect.token env T_LCURLY;
        let props = properties env (SMap.empty, []) in
        let end_loc = Peek.loc env in
        Expect.token env T_RCURLY;
        env, (Loc.btwn start_loc end_loc, Ast.Expression.Object.({
          properties = props;
        }))

    let rec _class env =
      let superClass, superTypeParameters =
        if Peek.token env = T_EXTENDS
        then begin
          Expect.token env T_EXTENDS;
          let prev_allow_yield = allow_yield env in
          let env = env |> with_allow_yield false in
          let env, superClass = Expression.left_hand_side env in
          let env = env |> with_allow_yield prev_allow_yield in
          let superTypeParameters = Type.type_parameter_instantiation env in
          Some superClass, superTypeParameters
        end else None, None in
      let implements =
        if Peek.token env = T_IMPLEMENTS
        then begin
          let env = if not (should_parse_types env)
            then error env Error.UnexpectedTypeInterface
            else env in
          Expect.token env T_IMPLEMENTS;
          class_implements env []
        end else [] in
      let body = class_body env in
      body, superClass, superTypeParameters, implements

    and class_implements env acc =
      let env, id = Parse.identifier env in
      let typeParameters = Type.type_parameter_instantiation env in
      let loc = match typeParameters with
      | None -> fst id
      | Some (loc, _) -> Loc.btwn (fst id) loc in
      let implement = loc, Ast.Class.Implements.({
        id;
        typeParameters;
      }) in
      let acc = implement::acc in
      match Peek.token env with
      | T_COMMA ->
          Expect.token env T_COMMA;
          class_implements env acc
      | _ -> List.rev acc

    and class_body =
      let rec elements env acc =
        match Peek.token env with
        | T_EOF
        | T_RCURLY -> env, List.rev acc
        | T_SEMICOLON ->
            (* Skip empty elements *)
            Expect.token env T_SEMICOLON;
            elements env acc
        | _ ->
            let env, element = class_element env in
            elements env (element::acc)

      in fun env ->
        let start_loc = Peek.loc env in
        Expect.token env T_LCURLY;
        let env, body = elements env [] in
        let end_loc = Peek.loc env in
        Expect.token env T_RCURLY;
        Loc.btwn start_loc end_loc, Ast.Class.Body.({
          body;
        })

    (* In the ES6 draft, all elements are methods. No properties (though there
     * are getter and setters allowed *)
    and class_element : env -> env * Ast.Class.Body.element =
      let get env start_loc decorators static =
        let key, (end_loc, _ as value) =
          _method env Ast.Expression.Object.Property.Get in
        env, Ast.Class.(Body.Method (Loc.btwn start_loc end_loc, Method.({
          key;
          value;
          kind = Get;
          static;
          decorators;
        })))

      in let set env start_loc decorators static =
        let key, (end_loc, _ as value) =
          _method env Ast.Expression.Object.Property.Set in
        env, Ast.Class.(Body.Method (Loc.btwn start_loc end_loc, Method.({
          key;
          value;
          kind = Set;
          static;
          decorators;
        })))

      in let init env start_loc decorators key async generator static =
        match Peek.token env with
        | T_COLON
        | T_ASSIGN
        | T_SEMICOLON when not async && not generator ->
          (* Class property with annotation *)
          let typeAnnotation = Type.annotation_opt env in
          let options = parse_options env in
          let env, value =
            if Peek.token env = T_ASSIGN then (
              if static && options.esproposal_class_static_fields
                 || (not static) && options.esproposal_class_instance_fields
              then begin
                Expect.token env T_ASSIGN;
                let env, value = Parse.expression env in
                env, Some value
              end else env, None
            ) else env, None in
          let end_loc = Peek.loc env in
          let env =
            if Expect.maybe env T_SEMICOLON then env
            else
              if Peek.token ~i:1 env == T_LBRACKET ||
                 Peek.token ~i:1 env == T_LPAREN
              then error_unexpected env
              else env
          in
          let loc = Loc.btwn start_loc end_loc in
          env, Ast.Class.(Body.Property (loc, Property.({
            key;
            value;
            typeAnnotation;
            static;
          })))
        | _ ->
          let typeParameters = Type.type_parameter_declaration env in
          let env, params, defaults, rest = Declaration.function_params env in
          let returnType = Type.annotation_opt env in
          let env, (_, body, strict) =
            Declaration.function_body env ~async ~generator in
          let simple =
            Declaration.is_simple_function_params params defaults rest in
          Declaration.strict_post_check env ~strict ~simple None params;
          let end_loc, expression = Function.(
            match body with
            | BodyBlock (loc, _) -> loc, false
            | BodyExpression (loc, _) -> loc, true) in
          let value = end_loc, Function.({
            id = None;
            params;
            defaults;
            rest;
            body;
            generator;
            async;
            expression;
            returnType;
            typeParameters;
          }) in
          let kind = Ast.(match key with
            | Expression.Object.Property.Identifier (_, {
                Identifier.name = "constructor";
                _;
              })
            | Expression.Object.Property.Literal (_, {
                Literal.value = Literal.String "constructor";
                _;
              }) ->
              Class.Method.Constructor
            | _ ->
              Class.Method.Method) in
          env, Ast.Class.(Body.Method (Loc.btwn start_loc end_loc, Method.({
            key;
            value;
            kind;
            static;
            decorators;
          })))

      in fun env -> Ast.Expression.Object.Property.(
        let start_loc = Peek.loc env in
        let decorators = decorator_list env in
        let static = Expect.maybe env T_STATIC in
        let async =
          Peek.token ~i:1 env <> T_LPAREN &&
          Peek.token ~i:1 env <> T_COLON &&
          Declaration.async env in
        let env, generator = Declaration.generator env async in
        let env, obj_key = key env in
        match (async, generator, obj_key) with
        | false, false,
          (_, (Identifier (_, { Identifier.name = "get"; _ }) as key)) ->
            (match Peek.token env with
            | T_LESS_THAN
            | T_COLON
            | T_ASSIGN
            | T_SEMICOLON
            | T_LPAREN -> init env start_loc decorators key async generator static
            | _ -> get env start_loc decorators static )
        | false, false,
          (_, (Identifier (_, { Identifier.name = "set"; _ }) as key)) ->
            (match Peek.token env with
            | T_LESS_THAN
            | T_COLON
            | T_ASSIGN
            | T_SEMICOLON
            | T_LPAREN -> init env start_loc decorators key async generator static
            | _ -> set env start_loc decorators static)
        | _, _, (_, key) ->
            init env start_loc decorators key async generator static
      )

    let class_declaration env decorators =
      (* 10.2.1 says all parts of a class definition are strict *)
      let env = env |> with_strict true in
      let start_loc = Peek.loc env in
      let decorators = decorators @ (decorator_list env) in
      Expect.token env T_CLASS;
      let prev_no_let = no_let env in
      let env = env |> with_no_let true in
      let env, id = (
        match in_export env, Peek.identifier env with
        | true, false -> env, None
        | _ ->
          let env, id = Parse.identifier env in
          env, Some id
      ) in
      let env = env |> with_no_let prev_no_let in
      let typeParameters = Type.type_parameter_declaration_with_defaults env in
      let body, superClass, superTypeParameters, implements = _class env in
      let loc = Loc.btwn start_loc (fst body) in
      env, (loc, Ast.Statement.(ClassDeclaration Class.({
        id;
        body;
        superClass;
        typeParameters;
        superTypeParameters;
        implements;
        classDecorators=decorators;
      })))

    let class_expression env : env * Ast.Expression.t =
      let start_loc = Peek.loc env in
      let decorators = decorator_list env in
      Expect.token env T_CLASS;
      let id, typeParameters = match Peek.token env with
        | T_EXTENDS
        | T_LESS_THAN
        | T_LCURLY -> None, None
        | _ ->
            let env, id = Parse.identifier env in
            let id = Some id in
            let typeParameters = Type.type_parameter_declaration_with_defaults env in
            id, typeParameters in
      let body, superClass, superTypeParameters, implements = _class env in
      let loc = Loc.btwn start_loc (fst body) in
      let expr = loc, Ast.Expression.(Class Class.({
        id;
        body;
        superClass;
        typeParameters;
        superTypeParameters;
        implements;
        classDecorators=decorators;
      })) in
      env, expr

    let key = key ~allow_computed_key:false
  end

  module Statement: sig
    val _for: env -> env * Ast.Statement.t
    val _if: env -> env * Ast.Statement.t
    val _let: env -> env * Ast.Statement.t
    val _try: env -> env * Ast.Statement.t
    val _while: env -> env * Ast.Statement.t
    val _with: env -> env * Ast.Statement.t
    val block: env -> env * Ast.Statement.t
    val break: env -> env * Ast.Statement.t
    val continue: env -> env * Ast.Statement.t
    val debugger: env -> env * Ast.Statement.t
    val declare: ?in_module:bool -> env -> env * Ast.Statement.t
    val declare_export_declaration: env -> env * Ast.Statement.t
    val do_while: env -> env * Ast.Statement.t
    val empty: env -> env * Ast.Statement.t
    val export_declaration: env -> Ast.Expression.t list -> env * Ast.Statement.t
    val expression: env -> env * Ast.Statement.t
    val import_declaration: env -> env * Ast.Statement.t
    val interface: env -> env * Ast.Statement.t
    val maybe_labeled: env -> env * Ast.Statement.t
    val return: env -> env * Ast.Statement.t
    val switch: env -> env * Ast.Statement.t
    val throw: env -> env * Ast.Statement.t
    val type_alias: env -> env * Ast.Statement.t
    val var_or_const: env -> env * Ast.Statement.t
  end = struct
    let rec empty env =
      let loc = Peek.loc env in
      Expect.token env T_SEMICOLON;
      env, (loc, Statement.Empty)

    and break env =
      let start_loc = Peek.loc env in
      Expect.token env T_BREAK;
      let env, label =
        if Peek.token env = T_SEMICOLON || Peek.is_implicit_semicolon env
        then env, None
        else begin
          let env, label = Parse.identifier env in
          let name = (snd label).Identifier.name in
          let env = if not (SSet.mem name (labels env))
            then error env (Error.UnknownLabel name)
            else env in
          env, Some label
        end
      in
      let end_loc = match Peek.semicolon_loc env with
      | Some loc -> loc
      | None -> (match label with
        | Some id -> fst id
        | None -> start_loc) in
      let loc = Loc.btwn start_loc end_loc in
      let env = if label = None && not (in_loop env || in_switch env)
        then error_at env (loc, Error.IllegalBreak)
        else env in
      let env = Eat.semicolon env in
      env, (loc, Statement.Break {
        Statement.Break.label = label;
      })

    and continue env =
      let start_loc = Peek.loc env in
      Expect.token env T_CONTINUE;
      let env, label =
        if Peek.token env = T_SEMICOLON || Peek.is_implicit_semicolon env
        then env, None
        else begin
          let env, label = Parse.identifier env in
          let (_, { Identifier.name; _ }) = label in
          let env = if not (SSet.mem name (labels env))
            then error env (Error.UnknownLabel name)
            else env in
          env, Some label
        end in
      let end_loc = match Peek.semicolon_loc env with
      | Some loc -> loc
      | None -> (match label with
        | Some id -> fst id
        | None -> start_loc) in
      let loc = Loc.btwn start_loc end_loc in
      let env = if not (in_loop env)
        then error_at env (loc, Error.IllegalContinue)
        else env in
      let env = Eat.semicolon env in
      env, (loc, Statement.Continue {
        Statement.Continue.label = label;
      })

    and debugger env =
      let start_loc = Peek.loc env in
      Expect.token env T_DEBUGGER;
      let end_loc = match Peek.semicolon_loc env with
      | None -> start_loc
      | Some loc -> loc in
      let env = Eat.semicolon env in
      env, (Loc.btwn start_loc end_loc, Statement.Debugger)

    and do_while env =
      let start_loc = Peek.loc env in
      Expect.token env T_DO;
      let prev_in_loop = in_loop env in
      let env = env |> with_in_loop true in
      let env, body = Parse.statement env in
      let env = env |> with_in_loop prev_in_loop in
      Expect.token env T_WHILE;
      Expect.token env T_LPAREN;
      let env, test = Parse.expression env in
      let end_loc = Peek.loc env in
      Expect.token env T_RPAREN;
      let end_loc = match Peek.semicolon_loc env with
      | None -> end_loc
      | Some loc -> loc in
      (* The rules of automatic semicolon insertion in ES5 don't mention this,
       * but the semicolon after a do-while loop is optional. This is properly
       * specified in ES6 *)
      let env = if Peek.token env = T_SEMICOLON
        then Eat.semicolon env
        else env in
      env, (Loc.btwn start_loc end_loc, Statement.(DoWhile DoWhile.({
        body;
        test;
      })))

    and _for =
      let assert_can_be_forin_or_forof env err = Statement.VariableDeclaration.(function
        | Some (Statement.For.InitDeclaration (loc, {
          declarations;
          _;
        })) ->
            (* Only a single declarator is allowed, without an init. So
             * something like
             *
             * for (var x in y) {}
             *
             * is allowed, but we disallow
             *
             * for (var x, y in z) {}
             * for (var x = 42 in y) {}
             *)
            let env = match declarations with
            | [ (_, { Declarator.init = None; _; }) ] -> env
            | _ -> error_at env (loc, err)
            in
            env
        | Some (Statement.For.InitExpression (loc, expr)) ->
            (* Only certain expressions can be the lhs of a for in or for of *)
            if not (Parse.is_assignable_lhs (loc, expr))
              then error_at env (loc, err)
              else env
        | _ -> error env err
      ) in

      fun env ->
        let start_loc = Peek.loc env in
        Expect.token env T_FOR;
        Expect.token env T_LPAREN;

        let env, init, errs =
          match Peek.token env with
          | T_SEMICOLON -> env, None, []
          | T_LET ->
              let env, decl, errs = Declaration._let (env |> with_no_in true) in
              env, Some (Statement.For.InitDeclaration decl), errs
          | T_CONST ->
              let env, decl, errs = Declaration.const (env |> with_no_in true) in
              env, Some (Statement.For.InitDeclaration decl), errs
          | T_VAR ->
              let env, decl, errs = Declaration.var (env |> with_no_in true) in
              env, Some (Statement.For.InitDeclaration decl), errs
          | _ ->
              let prev_no_in = no_in env in
              let prev_no_let = no_let env in
              let env = env |> with_no_in true |> with_no_let true in
              let env, expr = Parse.expression env in
              let env = env |> with_no_in prev_no_in |> with_no_let prev_no_let in
              env, Some (Statement.For.InitExpression expr), []
        in

        match Peek.token env with
        | T_IN ->
            let env =
              assert_can_be_forin_or_forof env Error.InvalidLHSInForIn init in
            let left = Statement.(match init with
            | Some (For.InitDeclaration decl) -> ForIn.LeftDeclaration decl
            | Some (For.InitExpression expr) -> ForIn.LeftExpression expr
            | None -> assert false) in
            (* This is a for in loop *)
            Expect.token env T_IN;
            let env, right = Parse.expression env in
            Expect.token env T_RPAREN;
            let prev_in_loop = in_loop env in
            let env = env |> with_in_loop true in
            let env, body = Parse.statement env in
            let env = env |> with_in_loop prev_in_loop in
            env, (Loc.btwn start_loc (fst body), Statement.(ForIn ForIn.({
              left;
              right;
              body;
              each = false;
            })))
        | T_OF ->
            let env =
              assert_can_be_forin_or_forof env Error.InvalidLHSInForOf init in
            let left = Statement.(match init with
            | Some (For.InitDeclaration decl) -> ForOf.LeftDeclaration decl
            | Some (For.InitExpression expr) -> ForOf.LeftExpression expr
            | None -> assert false) in
            (* This is a for of loop *)
            Expect.token env T_OF;
            let env, right = Parse.assignment env in
            Expect.token env T_RPAREN;
            let prev_in_loop = in_loop env in
            let env = env |> with_in_loop true in
            let env, body = Parse.statement env in
            let env = env |> with_in_loop prev_in_loop in
            env, (Loc.btwn start_loc (fst body), Statement.(ForOf ForOf.({
              left;
              right;
              body;
            })))
        | _ ->
            (* This is a for loop *)
            let env = List.fold_left error_at env errs in
            Expect.token env T_SEMICOLON;
            let env, test = match Peek.token env with
            | T_SEMICOLON -> env, None
            | _ -> let env, expr = Parse.expression env in env, Some expr in
            Expect.token env T_SEMICOLON;
            let env, update = match Peek.token env with
            | T_RPAREN -> env, None
            | _ -> let env, expr = Parse.expression env in env, Some expr in
            Expect.token env T_RPAREN;
            let prev_in_loop = in_loop env in
            let env = env |> with_in_loop true in
            let env, body = Parse.statement env in
            let env = env |> with_in_loop prev_in_loop in
            env, (Loc.btwn start_loc (fst body), Statement.(For For.({
              init;
              test;
              update;
              body;
            })))

    and _if env =
      let start_loc = Peek.loc env in
      Expect.token env T_IF;
      Expect.token env T_LPAREN;
      let env, test = Parse.expression env in
      Expect.token env T_RPAREN;
      let env, consequent = match Peek.token env with
      | _ when Peek._function env ->
          let env = strict_error env Error.StrictFunctionStatement in
          Declaration._function env
      | _ -> Parse.statement env in
      let env, alternate =
        if Peek.token env = T_ELSE then
          let () = Expect.token env T_ELSE in
          let env, alternate = Parse.statement env in
          env, Some alternate
        else
          env, None
      in
      let end_loc = match alternate with
      | Some stmt -> fst stmt
      | None -> fst consequent in
      env, (Loc.btwn start_loc end_loc, Statement.(If If.({
        test;
        consequent;
        alternate;
      })))

    and return env =
      let env = if not (in_function env)
        then error env Error.IllegalReturn
        else env in
      let start_loc = Peek.loc env in
      Expect.token env T_RETURN;
      let env, argument =
        if Peek.token env = T_SEMICOLON || Peek.is_implicit_semicolon env
        then env, None
        else let env, expr = Parse.expression env in env, Some expr in
      let end_loc = match Peek.semicolon_loc env with
      | Some loc -> loc
      | None -> (match argument with
        | Some argument -> fst argument
        | None -> start_loc) in
      let env = Eat.semicolon env in
      env, (Loc.btwn start_loc end_loc, Statement.(Return Return.({
        argument;
      })))

    and switch =
      let rec case_list env (seen_default, acc) =
        match Peek.token env with
        | T_EOF
        | T_RCURLY -> List.rev acc
        | _ ->
          let start_loc = Peek.loc env in
          let env, test = match Peek.token env with
          | T_DEFAULT ->
              let env = if seen_default
                then error env Error.MultipleDefaultsInSwitch
                else env in
              Expect.token env T_DEFAULT;
              env, None
          | _ ->
              Expect.token env T_CASE;
              let env, expr = Parse.expression env in
              env, Some expr
          in
          let seen_default = seen_default || test = None in
          let end_loc = Peek.loc env in
          Expect.token env T_COLON;
          let term_fn = function
          | T_RCURLY | T_DEFAULT | T_CASE -> true
          | _ -> false in
          let prev_in_switch = in_switch env in
          let env = env |> with_in_switch true in
          let env, consequent = Parse.statement_list ~term_fn env in
          let env = env |> with_in_switch prev_in_switch in
          let end_loc = match List.rev consequent with
          | last_stmt::_ -> fst last_stmt
          | _ -> end_loc in
          let acc = (Loc.btwn start_loc end_loc, Statement.Switch.Case.({
            test;
            consequent;
          }))::acc in
          case_list env (seen_default, acc)

      in fun env ->
        let start_loc = Peek.loc env in
        Expect.token env T_SWITCH;
        Expect.token env T_LPAREN;
        let env, discriminant = Parse.expression env in
        Expect.token env T_RPAREN;
        Expect.token env T_LCURLY;
        let cases = case_list env (false, []) in
        let end_loc = Peek.loc env in
        Expect.token env T_RCURLY;
        env, (Loc.btwn start_loc end_loc, Statement.(Switch Switch.({
          discriminant;
          cases;
          lexical = false; (* TODO *)
        })))

    and throw env =
      let start_loc = Peek.loc env in
      Expect.token env T_THROW;
      let env = if Peek.line_terminator env
        then error_at env (start_loc, Error.NewlineAfterThrow)
        else env in
      let env, argument = Parse.expression env in
      let end_loc = match Peek.semicolon_loc env with
      | Some loc -> loc
      | None -> fst argument in
      let env = Eat.semicolon env in
      env, (Loc.btwn start_loc end_loc, Statement.(Throw Throw.({
        argument;
      })))

    and _try env =
      let start_loc = Peek.loc env in
      Expect.token env T_TRY;
      let env, block = Parse.block_body env in
      let env, handler = match Peek.token env with
      | T_CATCH ->
          let start_loc = Peek.loc env in
          Expect.token env T_CATCH;
          Expect.token env T_LPAREN;
          let env, id = Parse.identifier ~restricted_error:Error.StrictCatchVariable env in
          let param = fst id, Pattern.Identifier id in
          Expect.token env T_RPAREN;
          let env, body = Parse.block_body env in
          let loc = Loc.btwn start_loc (fst body) in
          env, Some (loc, Ast.Statement.Try.CatchClause.({
            param;
            (* This SpiderMonkey specific feature is not on track to be in a
            * standard so I'm not supporting it *)
            guard = None;
            body;
          }))
      | _ -> env, None in
      (* SpiderMonkey feature, not supported in ES6 *)
      let guardedHandlers = [] in
      let env, finalizer = match Peek.token env with
      | T_FINALLY ->
          Expect.token env T_FINALLY;
          let env, body = Parse.block_body env in
          env, Some body
      | _ -> env, None in
      let env, end_loc = match finalizer with
      | Some finalizer -> env, fst finalizer
      | None ->
          (match handler with
          | Some handler -> env, fst handler
          | None ->
              (* No catch or finally? That's an error! *)
              let env = error_at env (fst block, Error.NoCatchOrFinally) in
              env, fst block) in
      env, (Loc.btwn start_loc end_loc, Statement.(Try Try.({
        block;
        handler;
        guardedHandlers;
        finalizer;
      })))

    and var_or_const env =
      let env, (start_loc, declaration), errs = Declaration.variable env in
      let end_loc = match Peek.semicolon_loc env with
      | None -> start_loc
      | Some end_loc -> end_loc in
      let env = Eat.semicolon env in
      let env = List.fold_left error_at env errs in
      env, (Loc.btwn start_loc end_loc, declaration)

    and _let env =
      let start_loc = Peek.loc env in
      Expect.token env T_LET;
      if Peek.token env = T_LPAREN
      then begin
        (* Let statement *)
        Expect.token env T_LPAREN;
        let prev_no_let = no_let env in
        let env = env |> with_no_let true in
        let env, end_loc, declarations, errs =
          Declaration.variable_declaration_list env in
        let env = env |> with_no_let prev_no_let in
        let head = List.map
          (fun (_, {Ast.Statement.VariableDeclaration.Declarator.id; init;}) ->
            Statement.Let.({ id; init; }))
          declarations in
        Expect.token env T_RPAREN;
        let env, body = Parse.statement env in
        let end_loc = match Peek.semicolon_loc env with
        | None -> end_loc
        | Some end_loc -> end_loc in
        let env = Eat.semicolon env in
        let env = List.fold_left error_at env errs in
        env, (Loc.btwn start_loc end_loc, Statement.(Let Let.({
          head;
          body;
        })))
      end else begin
        (* Let declaration *)
        let prev_no_let = no_let env in
        let env = env |> with_no_let true in
        let env, end_loc, declarations, errs =
          Declaration.variable_declaration_list env in
        let env = env |> with_no_let prev_no_let in
        let declaration =
          Ast.(Statement.VariableDeclaration Statement.VariableDeclaration.({
            declarations;
            kind = Let;
          })) in
        let end_loc = match Peek.semicolon_loc env with
        | None -> end_loc
        | Some end_loc -> end_loc in
        let env = Eat.semicolon env in
        let env = List.fold_left error_at env errs in
        env, (Loc.btwn start_loc end_loc, declaration)
      end

    and _while env =
      let start_loc = Peek.loc env in
      Expect.token env T_WHILE;
      Expect.token env T_LPAREN;
      let env, test = Parse.expression env in
      Expect.token env T_RPAREN;
      let prev_in_loop = in_loop env in
      let env = env |> with_in_loop true in
      let env, body = Parse.statement env in
      let env = env |> with_in_loop prev_in_loop in
      env, (Loc.btwn start_loc (fst body), Statement.(While While.({
        test;
        body;
      })))

    and _with env =
      let start_loc = Peek.loc env in
      Expect.token env T_WITH;
      Expect.token env T_LPAREN;
      let env, _object = Parse.expression env in
      Expect.token env T_RPAREN;
      let env, body = Parse.statement env in
      let loc = Loc.btwn start_loc (fst body) in
      let env = strict_error_at env (loc, Error.StrictModeWith) in
      env, (loc, Statement.(With With.({
        _object;
        body;
      })))

    and block env =
      let env, (loc, block) = Parse.block_body env in
      env, (loc, Statement.Block block)

    and maybe_labeled env =
      let env, expr = Parse.expression env in
      match (expr, Peek.token env) with
      | ((loc, Ast.Expression.Identifier label), T_COLON) ->
          let { Identifier.name; _ } = snd label in
          Expect.token env T_COLON;
          let env = if SSet.mem name (labels env)
            then error_at env (loc, Error.Redeclaration ("Label", name))
            else env in
          let env = add_label env name in
          let env, labeled_stmt = Parse.statement env in
          env, (Loc.btwn loc (fst labeled_stmt), Statement.Labeled {
            Statement.Labeled.label = label;
            Statement.Labeled.body = labeled_stmt;
          })
      | expression, _ ->
          let end_loc = match Peek.semicolon_loc env with
          | Some loc -> loc
          | None -> (fst expression) in
          let env = Eat.semicolon env in
          env, (Loc.btwn (fst expression) end_loc, Statement.(Expression Expression.({
            expression;
          })))

    and expression env =
      let env, expression = Parse.expression env in
      let end_loc = match Peek.semicolon_loc env with
      | Some loc -> loc
      | None -> fst expression in
      let env = Eat.semicolon env in
      env, (Loc.btwn (fst expression) end_loc, Statement.(Expression Expression.({
        expression;
      })))

    and type_alias_helper env =
      let start_loc = Peek.loc env in
      let env = if not (should_parse_types env)
        then error env Error.UnexpectedTypeAlias
        else env in
      Expect.token env T_TYPE;
      Eat.push_lex_mode env TYPE_LEX;
      let env, id = Parse.identifier env in
      let typeParameters = Type.type_parameter_declaration_with_defaults env in
      Expect.token env T_ASSIGN;
      (match Peek.token env with
      | T_BIT_OR | T_BIT_AND -> Eat.token env
      | _ -> ());
      let right = Type._type env in
      let end_loc = match Peek.semicolon_loc env with
      | None -> fst right
      | Some end_loc -> end_loc in
      let env = Eat.semicolon env in
      Eat.pop_lex_mode env;
      Loc.btwn start_loc end_loc, Statement.TypeAlias.({
        id;
        typeParameters;
        right;
      })

    and type_alias env =
      if Peek.identifier ~i:1 env
      then
        let loc, type_alias = type_alias_helper env in
        env, (loc, Statement.TypeAlias type_alias)
      else
        Parse.statement env

    and interface : env -> env * Ast.Statement.t =
      let rec supers env acc =
        let super = Type.generic env in
        let acc = super::acc in
        match Peek.token env with
        | T_COMMA ->
            Expect.token env T_COMMA;
            supers env acc
        | _ -> List.rev acc

      in fun env ->
        let start_loc = Peek.loc env in
        if Peek.identifier ~i:1 env
        then begin
          let env = if not (should_parse_types env)
            then error env Error.UnexpectedTypeInterface
            else env in
          Expect.token env T_INTERFACE;
          let env, id = Parse.identifier env in
          let typeParameters = Type.type_parameter_declaration_with_defaults env in
          let extends = if Peek.token env = T_EXTENDS
          then begin
            Expect.token env T_EXTENDS;
            supers env []
          end else [] in
          let env, body = Type._object ~allow_static:true env in
          let loc = Loc.btwn start_loc (fst body) in
          env, (loc, Statement.(InterfaceDeclaration Interface.({
            id;
            typeParameters;
            body;
            extends;
            mixins = [];
          })))
        end else begin
          expression env
        end

    and declare_class : env -> Loc.t -> env * (Loc.t * Ast.Statement.Interface.t) =
      let rec supers env acc =
        let super = Type.generic env in
        let acc = super::acc in
        match Peek.token env with
        | T_COMMA ->
          Expect.token env T_COMMA;
          supers env acc
        | _ -> List.rev acc

      (* This is identical to `interface`, except that mixins are allowed *)
      in fun env start_loc ->
        let env = env |> with_strict true in
        Expect.token env T_CLASS;
        let env, id = Parse.identifier env in
        let typeParameters = Type.type_parameter_declaration_with_defaults env in
        let extends = if Peek.token env = T_EXTENDS
          then begin
            Expect.token env T_EXTENDS;
            supers env []
          end else [] in
        let mixins = if Peek.value env = "mixins"
          then begin
            Expect.contextual env "mixins";
            supers env []
          end else [] in
        let env, body = Type._object ~allow_static:true env in
        let loc = Loc.btwn start_loc (fst body) in
        env, (loc, Statement.Interface.({
          id;
          typeParameters;
          body;
          extends;
          mixins;
        }))

    and declare_class_statement env start_loc =
      let env, (loc, fn) = declare_class env start_loc in
      env, (loc, Statement.DeclareClass fn)

    and declare_function env start_loc : env * (Loc.t * Ast.Statement.DeclareFunction.t) =
      Expect.token env T_FUNCTION;
      let env, id = Parse.identifier env in
      let start_sig_loc = Peek.loc env in
      let typeParameters = Type.type_parameter_declaration env in
      let rest, params = Type.function_param_list env in
      Expect.token env T_COLON;
      let returnType = Type._type env in
      let end_loc = fst returnType in
      let loc = Loc.btwn start_sig_loc end_loc in
      let value = loc, Ast.Type.(Function {Function.
        params;
        returnType;
        rest;
        typeParameters;
      }) in
      let typeAnnotation = Some ((fst value), value) in
      let id =
        Loc.btwn (fst id) end_loc,
        Ast.Identifier.({(snd id) with typeAnnotation; })
      in
      let end_loc = match Peek.semicolon_loc env with
      | None -> end_loc
      | Some end_loc -> end_loc in
      let env = Eat.semicolon env in
      let loc = Loc.btwn start_loc end_loc in
      env, (loc, Statement.DeclareFunction.({ id; }))

    and declare_function_statement env start_loc =
      let env, (loc, fn) = declare_function env start_loc in
      env, (loc, Statement.DeclareFunction fn)

    and declare_var env start_loc =
      Expect.token env T_VAR;
      let env, id = Parse.identifier_with_type env Error.StrictVarName in
      let end_loc = match Peek.semicolon_loc env with
      | None -> fst id
      | Some loc -> loc in
      let loc = Loc.btwn start_loc end_loc in
      let env = Eat.semicolon env in
      env, (loc, Statement.DeclareVariable.({ id; }))

    and declare_var_statement env start_loc =
      let env, (loc, var) = declare_var env start_loc in
      env, (loc, Statement.DeclareVariable var)

    and declare_module =
      let rec module_items env (acc: Ast.Statement.t list) : env * Ast.Statement.t list =
        match Peek.token env with
        | T_EOF
        | T_RCURLY -> env, List.rev acc
        | _ ->
          let env, stmt = declare ~in_module:true env in
          module_items env (stmt::acc)

      in fun env start_loc ->
        let env, id = match Peek.token env with
        | T_STRING (loc, value, raw, octal) ->
            let env = if octal
              then strict_error env Error.StrictOctalLiteral
              else env in
            Expect.token env (T_STRING (loc, value, raw, octal));
            let value = Literal.String value in
            env, Statement.DeclareModule.Literal (loc, { Literal.value; raw; })
        | _ ->
            let env, id = Parse.identifier env in
            env, Statement.DeclareModule.Identifier id in
        let body_start_loc = Peek.loc env in
        Expect.token env T_LCURLY;
        let env, body = module_items env [] in
        Expect.token env T_RCURLY;
        let body_end_loc = Peek.loc env in
        let body_loc = Loc.btwn body_start_loc body_end_loc in
        let body = body_loc, { Statement.Block.body; } in
        let loc = Loc.btwn start_loc (fst body) in
        env, (loc, Statement.(DeclareModule DeclareModule.({ id; body; })))

    and declare_module_exports env start_loc =
      Expect.token env T_PERIOD;
      Expect.contextual env "exports";
      let type_annot = Type.annotation env in
      let end_loc =
        match Peek.semicolon_loc env with
        | Some loc -> loc
        | None -> fst type_annot
      in
      let env = Eat.semicolon env in
      let loc = Loc.btwn start_loc end_loc in
      env, (loc, Statement.DeclareModuleExports type_annot)

    and declare ?(in_module=false) env : env * Ast.Statement.t =
      let env = if not (should_parse_types env)
        then error env Error.UnexpectedTypeDeclaration
        else env in
      let start_loc = Peek.loc env in
      (* eventually, just emit a wrapper AST node *)
      (match Peek.token ~i:1 env with
        | T_CLASS ->
            Expect.token env T_DECLARE;
            declare_class_statement env start_loc
        | T_INTERFACE ->
            Expect.token env T_DECLARE;
            interface env
        | T_TYPE ->
            Expect.token env T_DECLARE;
            type_alias env;
        | T_FUNCTION ->
            Expect.token env T_DECLARE;
            declare_function_statement env start_loc
        | T_VAR ->
            Expect.token env T_DECLARE;
            declare_var_statement env start_loc
        | T_ASYNC ->
            Expect.token env T_DECLARE;
            let env = error env Error.DeclareAsync in
            Expect.token env T_ASYNC;
            declare_function_statement env start_loc
        | T_IDENTIFIER when Peek.value ~i:1 env = "module" ->
            Expect.token env T_DECLARE;
            Expect.contextual env "module";
            if in_module || Peek.token env = T_PERIOD
            then declare_module_exports env start_loc
            else declare_module env start_loc
        | _ when in_module ->
            (* Oh boy, found some bad stuff in a declare module. Let's just
              * pretend it's a declare var (arbitrary choice) *)
            Expect.token env T_DECLARE;
            declare_var_statement env start_loc
        | _ ->
            Parse.statement env
      )

    let export_source env =
      Expect.contextual env "from";
      match Peek.token env with
      | T_STRING (loc, value, raw, octal) ->
          let env = if octal
            then strict_error env Error.StrictOctalLiteral
            else env in
          Expect.token env (T_STRING (loc, value, raw, octal));
          let value = Literal.String value in
          env, (loc, { Literal.value; raw; })
      | _ ->
          (* Just make up a string for the error case *)
          let raw = Peek.value env in
          let value = Literal.String raw in
          let ret = Peek.loc env, Literal.({ value; raw; }) in
          let env = error_unexpected env in
          env, ret

    let extract_pattern_binding_names =
      let rec fold acc = Pattern.(function
        | (_, Object {Object.properties; _;}) ->
          List.fold_left (fun acc prop ->
            match prop with
            | Object.Property (_, {Object.Property.pattern; _;})
            | Object.SpreadProperty (_, {Object.SpreadProperty.argument = pattern;})
              -> fold acc pattern
          ) acc properties
        | (_, Array {Array.elements; _;}) ->
          List.fold_left (fun acc elem ->
            match elem with
            | Some (Array.Element pattern)
            | Some (Array.Spread (_, {Array.SpreadElement.argument = pattern;}))
              -> fold acc pattern
            | None -> acc
          ) acc elements
        | (_, Assignment {Assignment.left;_;}) -> fold acc left
        | (_, Identifier (loc, {Identifier.name; _;})) -> (loc, name)::acc
        | (_, Expression _) ->
          failwith "Parser error: No such thing as an expression pattern!"
      ) in
      List.fold_left fold

    let extract_ident_name (_, {Identifier.name; _;}) = name

    let rec export_specifiers_and_errs env specifiers errs =
      match Peek.token env with
      | T_EOF
      | T_RCURLY ->
          List.rev specifiers, List.rev errs
      | _ ->
          let env, id, err = Parse.identifier_or_reserved_keyword env in
          let env, name, err, end_loc = if Peek.value env = "as"
          then begin
            Expect.contextual env "as";
            let env, name, _ = Parse.identifier_or_reserved_keyword env in
            let env = record_export env (fst name, extract_ident_name name) in
            env, Some name, None, fst name
          end else begin
            let loc = fst id in
            let env = record_export env (loc, extract_ident_name id) in
            env, None, err, loc
          end in
          let loc = Loc.btwn (fst id) end_loc in
          let specifier = loc, {
            Statement.ExportDeclaration.Specifier.id;
            name;
          } in
          if Peek.token env = T_COMMA
          then Expect.token env T_COMMA;
          let errs = match err with
          | Some err -> err::errs
          | None -> errs in
          export_specifiers_and_errs env (specifier::specifiers) errs

    let export_declaration env decorators =
      let env = env |> with_strict true |> with_in_export true in
      let start_loc = Peek.loc env in
      Expect.token env T_EXPORT;
      Statement.ExportDeclaration.(match Peek.token env with
      | T_DEFAULT ->
          (* export default ... *)
          Expect.token env T_DEFAULT;
          let env = record_export env (Loc.btwn start_loc (Peek.loc env), "default") in
          let env, end_loc, declaration = match Peek.token env with
          | T_FUNCTION ->
              (* export default function foo (...) { ... } *)
              let env, fn = Declaration._function env in
              env, fst fn, Some (Declaration fn)
          | _ when Peek._class env ->
              (* export default class foo { ... } *)
              let env, _class = Object.class_declaration env decorators in
              env, fst _class, Some (Declaration _class)
          | _ ->
              (* export default [assignment expression]; *)
              let env, expr = Parse.assignment env in
              let end_loc = match Peek.semicolon_loc env with
              | Some loc -> loc
              | None -> fst expr in
              let env = Eat.semicolon env in
              env, end_loc, Some (Expression expr)
            in
          env, (Loc.btwn start_loc end_loc, Statement.ExportDeclaration {
            default = true;
            declaration;
            specifiers = None;
            source = None;
            exportKind = ExportValue;
          })
      | T_TYPE when (Peek.token env ~i:1) <> T_LCURLY ->
          (* export type ... *)
          let env = if not (should_parse_types env)
            then error env Error.UnexpectedTypeExport
            else env in
          let env, type_alias = type_alias env in
          let env = match type_alias with
            | (loc, Statement.TypeAlias {Statement.TypeAlias.id; _;}) ->
              record_export env (loc, extract_ident_name id)
            | _ -> failwith (
                "Internal Flow Error! Parsed `export type` into something " ^
                "other than a type alias!"
              )
          in
          let end_loc = fst type_alias in
          env, (Loc.btwn start_loc end_loc, Statement.ExportDeclaration {
            default = false;
            declaration = Some (Declaration type_alias);
            specifiers = None;
            source = None;
            exportKind = ExportType;
          })
      | T_INTERFACE ->
          (* export interface I { ... } *)
          let env = if not (should_parse_types env)
            then error env Error.UnexpectedTypeExport
            else env in
          let env, interface = interface env in
          let env = match interface with
            | (loc, Statement.InterfaceDeclaration {Statement.Interface.id; _;}) ->
              record_export env (loc, extract_ident_name id)
            | _ -> failwith (
                "Internal Flow Error! Parsed `export interface` into something " ^
                "other than an interface declaration!"
              )
          in
          let end_loc = fst interface in
          env, (Loc.btwn start_loc end_loc, Statement.ExportDeclaration {
            default = false;
            declaration = Some (Declaration interface);
            specifiers = None;
            source = None;
            exportKind = ExportType;
          })
      | T_LET
      | T_CONST
      | T_VAR
      (* not using Peek._class here because it would guard all of the
        * cases *)
      | T_AT
      | T_CLASS
      (* not using Peek._function here because it would guard all of the
        * cases *)
      | T_ASYNC
      | T_FUNCTION ->
          let env, stmt = Parse.statement_list_item env ~decorators:decorators in
          let env, names = Statement.(
            match stmt with
            | (_, VariableDeclaration { VariableDeclaration.declarations; _; }) ->
              env, List.fold_left (fun names (_, declaration) ->
                let id = declaration.VariableDeclaration.Declarator.id in
                extract_pattern_binding_names names [id]
              ) [] declarations
            | (loc, ClassDeclaration { Class.id = Some id; _; })
            | (loc, FunctionDeclaration { Function.id = Some id; _; })
              -> env, [(loc, extract_ident_name id)]
            | (loc, ClassDeclaration { Class.id = None; _; }) ->
              let env = error_at env (loc, Error.ExportNamelessClass) in
              env, []
            | (loc, FunctionDeclaration { Function.id = None; _; }) ->
              let env = error_at env (loc, Error.ExportNamelessFunction) in
              env, []
            | _ -> failwith "Internal Flow Error! Unexpected export statement declaration!"
          ) in
          let env = List.fold_left record_export env names in
          let declaration = Some (Declaration stmt) in
          env, (Loc.btwn start_loc (fst stmt), Statement.ExportDeclaration {
            default = false;
            declaration;
            specifiers = None;
            source = None;
            exportKind = ExportValue;
          })
      | T_MULT ->
          let loc = Peek.loc env in
          Expect.token env T_MULT;
          let env, local_name =
            let parse_export_star_as =
              (parse_options env).esproposal_export_star_as
            in
            if Peek.value env = "as"
            then (
              Expect.contextual env "as";
              if parse_export_star_as
              then
                let env, id = Parse.identifier env in
                (env, Some id)
              else (error env Error.UnexpectedTypeDeclaration, None)
            ) else env, None
          in
          let specifiers =
            Some (ExportBatchSpecifier (loc, local_name))
          in
          let env, source = export_source env in
          let end_loc = match Peek.semicolon_loc env with
          | Some loc -> loc
          | None -> fst source in
          let source = Some source in
          let env = Eat.semicolon env in
          env, (Loc.btwn start_loc end_loc, Statement.ExportDeclaration {
            default = false;
            declaration = None;
            specifiers;
            source;
            exportKind = ExportValue;
          })
      | _ ->
          let exportKind = (
            match Peek.token env with
            | T_TYPE -> Eat.token env; ExportType
            | _ -> ExportValue
          ) in
          Expect.token env T_LCURLY;
          let specifiers, errs = export_specifiers_and_errs env [] [] in
          let specifiers = Some (ExportSpecifiers specifiers) in
          let end_loc = Peek.loc env in
          Expect.token env T_RCURLY;
          let env, source = if Peek.value env = "from"
          then
            let env, source = export_source env in
            env, Some source
          else begin
            let env = List.fold_left error_at env errs in
            env, None
          end in
          let end_loc = match Peek.semicolon_loc env with
          | Some loc -> loc
          | None ->
              (match source with
              | Some source -> fst source
              | None -> end_loc) in
          let env = Eat.semicolon env in
          env, (Loc.btwn start_loc end_loc, Statement.ExportDeclaration {
            default = false;
            declaration = None;
            specifiers;
            source;
            exportKind;
          })
      )

    and declare_export_declaration env =
      let env = if not (should_parse_types env)
        then error env Error.UnexpectedTypeDeclaration
        else env in
      let start_loc = Peek.loc env in
      Expect.token env T_DECLARE;

      let env = env |> with_strict true |> with_in_export true in
      Expect.token env T_EXPORT;
      Statement.DeclareExportDeclaration.(match Peek.token env with
      | T_DEFAULT ->
          (* declare export default ... *)
          Expect.token env T_DEFAULT;
          let env, end_loc, declaration = match Peek.token env with
          | T_FUNCTION ->
              (* declare export default function foo (...): ...  *)
              let env, fn = declare_function env start_loc in
              env, fst fn, Some (Function fn)
          | T_CLASS ->
              (* declare export default class foo { ... } *)
              let env, _class = declare_class env start_loc in
              env, fst _class, Some (Class _class)
          | _ ->
              (* declare export default [type]; *)
              let _type = Type._type env in
              let end_loc = match Peek.semicolon_loc env with
              | Some loc -> loc
              | None -> fst _type in
              let env = Eat.semicolon env in
              env, end_loc, Some (DefaultType _type)
            in
          env, (Loc.btwn start_loc end_loc, Statement.DeclareExportDeclaration {
            default = true;
            declaration;
            specifiers = None;
            source = None;
          })
      | T_LET
      | T_CONST
      | T_VAR
      | T_CLASS
      | T_FUNCTION ->
          let env, end_loc, declaration = match Peek.token env with
          | T_FUNCTION ->
              (* declare export function foo (...): ...  *)
              let env, fn = declare_function env start_loc in
              env, fst fn, Some (Function fn)
          | T_CLASS ->
              (* declare export class foo { ... } *)
              let env, _class = declare_class env start_loc in
              env, fst _class, Some (Class _class)
          | T_LET
          | T_CONST
          | T_VAR as token ->
              let env = match token with
              | T_LET -> error env Error.DeclareExportLet
              | T_CONST -> error env Error.DeclareExportConst
              | _ -> env
              in
              (* declare export var foo: ... *)
              let env, var = declare_var env start_loc in
              env, fst var, Some (Variable var)
          | _ -> assert false in
          env, (Loc.btwn start_loc end_loc, Statement.DeclareExportDeclaration {
            default = false;
            declaration;
            specifiers = None;
            source = None;
          })
      | T_MULT ->
          (* declare export * from 'foo' *)
          let loc = Peek.loc env in
          Expect.token env T_MULT;
          let parse_export_star_as =
            (parse_options env).esproposal_export_star_as
          in
          let env, local_name =
            if Peek.value env = "as"
            then (
              Expect.contextual env "as";
              if parse_export_star_as
              then
                let env, id = Parse.identifier env in
                env, Some id
              else (error env Error.UnexpectedTypeDeclaration, None)
            ) else env, None
          in
          let specifiers = Statement.ExportDeclaration.(
            Some (ExportBatchSpecifier (loc, local_name))
          ) in
          let env, source = export_source env in
          let end_loc = match Peek.semicolon_loc env with
          | Some loc -> loc
          | None -> fst source in
          let source = Some source in
          let env = Eat.semicolon env in
          env, (Loc.btwn start_loc end_loc, Statement.DeclareExportDeclaration {
            default = false;
            declaration = None;
            specifiers;
            source;
          })
      | _ ->
          let env = match Peek.token env with
            | T_TYPE -> error env Error.DeclareExportType
            | T_INTERFACE -> error env Error.DeclareExportInterface
            | _ -> env
          in
          Expect.token env T_LCURLY;
          let specifiers, errs = export_specifiers_and_errs env [] [] in
          let specifiers = Some (Statement.ExportDeclaration.ExportSpecifiers specifiers) in
          let end_loc = Peek.loc env in
          Expect.token env T_RCURLY;
          let env, source =
            if Peek.value env = "from" then
              let env, source = export_source env in
              env, Some source
            else
              let env = List.fold_left error_at env errs in
              env, None
          in
          let end_loc = match Peek.semicolon_loc env with
          | Some loc -> loc
          | None ->
              (match source with
              | Some source -> fst source
              | None -> end_loc) in
          let env = Eat.semicolon env in
          env, (Loc.btwn start_loc end_loc, Statement.DeclareExportDeclaration {
            default = false;
            declaration = None;
            specifiers;
            source;
          })
      )

    and import_declaration =
      let open Statement.ImportDeclaration in

      let source env : env * (Loc.t * Ast.Literal.t) =
        Expect.contextual env "from";
        match Peek.token env with
        | T_STRING (loc, value, raw, octal) ->
            let env = if octal
              then strict_error env Error.StrictOctalLiteral
              else env in
            Expect.token env (T_STRING (loc, value, raw, octal));
            let value = Literal.String value in
            env, (loc, { Literal.value; raw; })
        | _ ->
            (* Just make up a string for the error case *)
            let raw = Peek.value env in
            let value = Literal.String raw in
            let ret = Peek.loc env, Literal.({ value; raw; }) in
            let env = error_unexpected env in
            env, ret

      in let rec specifier_list
          (env: env)
          (acc: Ast.Statement.ImportDeclaration.specifier list)
          : env * Ast.Statement.ImportDeclaration.specifier list =
        match Peek.token env with
        | T_EOF
        | T_RCURLY -> env, List.rev acc
        | _ ->
            let env, remote, err = Parse.identifier_or_reserved_keyword env in
            let env, specifier =
              if Peek.value env = "as" then begin
                Expect.contextual env "as";
                let env, id = Parse.identifier env in
                let local = Some id in
                env, ImportNamedSpecifier { local; remote; }
              end else begin
                let env = match err with
                  | Some err -> error_at env err
                  | None -> env
                in
                env, ImportNamedSpecifier { local = None; remote; }
              end
            in
            if Peek.token env = T_COMMA
            then Expect.token env T_COMMA;
            specifier_list env (specifier::acc)

      in let named_or_namespace_specifier env =
        let start_loc = Peek.loc env in
        match Peek.token env with
        | T_MULT ->
            Expect.token env T_MULT;
            Expect.contextual env "as";
            let env, id = Parse.identifier env in
            env, [ImportNamespaceSpecifier (Loc.btwn start_loc (fst id), id)]
        | _ ->
            Expect.token env T_LCURLY;
            let env, specifiers = specifier_list env [] in
            Expect.token env T_RCURLY;
            env, specifiers

      in fun env ->
        let env = env |> with_strict true in
        let start_loc = Peek.loc env in
        Expect.token env T_IMPORT;
        (* It might turn out that we need to treat this "type" token as an
         * identifier, like import type from "module" *)
        let env, importKind, type_ident =
          match Peek.token env with
          | T_TYPE ->
            let env = if not (should_parse_types env)
              then error env Error.UnexpectedTypeImport
              else env in
            let env, id = Parse.identifier env in
            env, ImportType, Some id
          | T_TYPEOF ->
            let env = if not (should_parse_types env)
              then error env Error.UnexpectedTypeImport
              else env in
            Expect.token env T_TYPEOF;
            env, ImportTypeof, None
          | _ -> env, ImportValue, None
        in
        match Peek.token env, Peek.identifier env with
        (* import "ModuleName"; *)
        | T_STRING (str_loc, value, raw, octal), _
            when importKind = ImportValue ->
          let env = if octal
            then strict_error env Error.StrictOctalLiteral
            else env in
          Expect.token env (T_STRING (str_loc, value, raw, octal));
          let value = Literal.String value in
          let source = (str_loc, { Literal.value; raw; }) in
          let end_loc = match Peek.semicolon_loc env with
          | Some loc -> loc
          | None -> str_loc in
          let env = Eat.semicolon env in
          env, (Loc.btwn start_loc end_loc, Statement.ImportDeclaration {
            importKind;
            source;
            specifiers = [];
          })

        (* import [type] SomeDefault ... *)
        | T_COMMA, _ (* `import type, ...` *)
        | _, true -> (* `import type Foo` or `import type from` *)
            let env, importKind, default_specifier = (
              match type_ident, Peek.token env, Peek.value env with
              | Some type_ident, T_COMMA, _ (* `import type,` *)
              | Some type_ident, T_IDENTIFIER, "from" -> (* `import type from` *)
                env, ImportValue, ImportDefaultSpecifier type_ident
              | _ -> (* Either `import type Foo` or `import Foo` *)
                let env, id = Parse.identifier env in
                env, importKind, ImportDefaultSpecifier id
            ) in

            let env, additional_specifiers = (
              match Peek.token env with
              | T_COMMA -> (* `import Foo, ...` *)
                  Expect.token env T_COMMA;
                  named_or_namespace_specifier env
              | _ -> env, []
            ) in

            let env, source = source env in
            let end_loc = match Peek.semicolon_loc env with
            | Some loc -> loc
            | None -> fst source in
            let source = source in
            let env = Eat.semicolon env in
            env, (Loc.btwn start_loc end_loc, Statement.ImportDeclaration {
              importKind;
              source;
              specifiers = default_specifier::additional_specifiers;
            })

        (* `import [type] { ... } ...` or `import [typeof] * as ...` *)
        | _ ->
            let env, specifiers = named_or_namespace_specifier env in
            let env, source = source env in
            let end_loc = match Peek.semicolon_loc env with
            | Some loc -> loc
            | None -> fst source in
            let source = source in
            let env = Eat.semicolon env in
            env, (Loc.btwn start_loc end_loc, Statement.ImportDeclaration {
              importKind;
              source;
              specifiers;
            })
  end

  module Pattern = struct
    (* Reinterpret various expressions as patterns.
     * This is not the correct thing to do and is only used for assignment
     * expressions. This should be removed and replaced ASAP.
     *)
    let object_from_expr =
      let property env prop =
        Ast.Expression.Object.(match prop with
        | Property (loc, { Property.key; value; shorthand; _ }) ->
          let key = Property.(match key with
          | Literal lit -> Pattern.Object.Property.Literal lit
          | Identifier id -> Pattern.Object.Property.Identifier id
          | Computed expr -> Pattern.Object.Property.Computed expr) in
          let env, pattern = Parse.pattern_from_expr env value in
          env, Pattern.(Object.Property (loc, Object.Property.({
            key;
            pattern;
            shorthand;
          })))
        | SpreadProperty (loc, { SpreadProperty.argument; }) ->
            let env, argument = Parse.pattern_from_expr env argument in
            env, Pattern.(Object.SpreadProperty (loc, Object.SpreadProperty.({
              argument;
            }))))

      in fun env (loc, obj) ->
        let env, rev_properties =
          List.fold_left (fun (env, properties) prop ->
            let env, prop = property env prop in
            env, prop::properties
          ) (env, []) obj.Ast.Expression.Object.properties
        in
        let properties = List.rev rev_properties in
        env, (loc, Pattern.(Object Object.({
          properties;
          typeAnnotation = None;
        })))

    let array_from_expr =
      let element env = Ast.Expression.(function
        | None -> env, None
        | Some (Spread (loc, spread)) ->
            let env, argument = Parse.pattern_from_expr env (spread.SpreadElement.argument) in
            env, Some Pattern.(Array.Spread (loc, { Array.SpreadElement.argument; }))
        | Some (Expression (loc, expr)) ->
            let env, element = Parse.pattern_from_expr env (loc, expr) in
            env, Some Pattern.Array.(Element element)
      )

      in fun env (loc, arr) ->
        let env, rev_elements =
          List.fold_left (fun (env, elements) elem ->
            let env, elem = element env elem in
            env, elem::elements
          ) (env, []) arr.Ast.Expression.Array.elements
        in
        let elements = List.rev rev_elements in
        env, (loc, Pattern.(Array Array.({
          elements;
          typeAnnotation = None;
        })))

    let from_expr env (loc, expr) : env * Ast.Pattern.t =
      Ast.Expression.(match expr with
      | Object obj -> object_from_expr env (loc, obj)
      | Array arr ->  array_from_expr env (loc, arr)
      | Identifier id -> env, (loc, Pattern.Identifier id)
      | Assignment { Assignment.operator = Assignment.Assign; left; right } ->
          env, (loc, Pattern.Assignment { Pattern.Assignment.left; right })
      | expr -> env, (loc, Pattern.Expression (loc, expr)))

    (* Parse object destructuring pattern *)
    let rec _object restricted_error : env -> env * Ast.Pattern.t =
      let rec property env : env * Ast.Pattern.Object.property option =
        let start_loc = Peek.loc env in
        if Expect.maybe env T_ELLIPSIS
        then begin
          let env, argument = pattern env restricted_error in
          let loc = Loc.btwn start_loc (fst argument) in
          env, Some Pattern.Object.(SpreadProperty (loc, SpreadProperty.({
            argument
          })))
        end else begin
          let env, key = Parse.object_key env in
          let key = Ast.Expression.Object.Property.(
            match key with
            | _, Literal lit -> Pattern.Object.Property.Literal lit
            | _, Identifier id -> Pattern.Object.Property.Identifier id
            | _, Computed expr -> Pattern.Object.Property.Computed expr
          ) in
          let env, prop = match Peek.token env with
            | T_COLON ->
              Expect.token env T_COLON;
              let env, pattern = pattern env restricted_error in
              env, Some (pattern, false)
            | _ ->
              (match key with
              | Pattern.Object.Property.Identifier id ->
                let pattern = (fst id, Pattern.Identifier id) in
                env, Some (pattern, true)
              | _ ->
                (* invalid shorthand destructuring *)
                let env = error_unexpected env in
                env, None)
          in
          match prop with
          | Some (pattern, shorthand) ->
            let env, pattern = match Peek.token env with
              | T_ASSIGN ->
                Expect.token env T_ASSIGN;
                let env, default = Parse.assignment env in
                let loc = Loc.btwn (fst pattern) (fst default) in
                env, (loc, Pattern.(Assignment Assignment.({
                  left = pattern;
                  right = default;
                })))
              | _ -> env, pattern
            in
            let loc = Loc.btwn start_loc (fst pattern) in
            env, Some Pattern.Object.(Property (loc, Property.({
              key;
              pattern;
              shorthand;
            })))
          | None -> env, None
        end

      and properties env acc =
        match Peek.token env with
        | T_EOF
        | T_RCURLY -> List.rev acc
        | _ ->
          let env, prop = property env in
          (match prop with
          | Some prop ->
            if Peek.token env <> T_RCURLY
            then Expect.token env T_COMMA;
            properties env (prop::acc)
          | None -> properties env acc)

      in fun env ->
        let start_loc = Peek.loc env in
        Expect.token env T_LCURLY;
        let properties = properties env [] in
        let end_loc = Peek.loc env in
        Expect.token env T_RCURLY;
        let end_loc, typeAnnotation =
          if Peek.token env = T_COLON then
            let typeAnnotation = Type.annotation env in
            fst typeAnnotation, Some typeAnnotation
          else end_loc, None
        in
        let loc = Loc.btwn start_loc end_loc in
        env, (loc, Pattern.(Object Object.({
          properties;
          typeAnnotation;
        })))

    (* Parse array destructuring pattern *)
    and _array restricted_error : env -> env * Ast.Pattern.t =
      let rec elements
          (env: env)
          (acc: Ast.Pattern.Array.element option list)
          : env * Ast.Pattern.Array.element option list =
        match Peek.token env with
        | T_EOF
        | T_RBRACKET -> env, List.rev acc
        | T_COMMA ->
          Expect.token env T_COMMA;
          elements env (None::acc)
        | T_ELLIPSIS ->
          let start_loc = Peek.loc env in
          Expect.token env T_ELLIPSIS;
          let env, argument = pattern env restricted_error in
          let loc = Loc.btwn start_loc (fst argument) in
          let element = Pattern.Array.(Spread (loc, SpreadElement.({
            argument;
          }))) in
          elements env ((Some element)::acc)
        | _ ->
          let env, pattern = pattern env restricted_error in
          let env, pattern = match Peek.token env with
            | T_ASSIGN ->
              Expect.token env T_ASSIGN;
              let env, default = Parse.expression env in
              let loc = Loc.btwn (fst pattern) (fst default) in
              let pattern = loc, Pattern.(Assignment Assignment.({
                left = pattern;
                right = default;
              })) in
              env, pattern
            | _ -> env, pattern
          in
          let element = Pattern.Array.(Element pattern) in
          if Peek.token env <> T_RBRACKET then Expect.token env T_COMMA;
          elements env ((Some element)::acc)

      in fun env ->
        let start_loc = Peek.loc env in
        Expect.token env T_LBRACKET;
        let env, elements = elements env [] in
        let end_loc = Peek.loc env in
        Expect.token env T_RBRACKET;
        let end_loc, typeAnnotation =
          if Peek.token env = T_COLON then
            let typeAnnotation = Type.annotation env in
            fst typeAnnotation, Some typeAnnotation
          else end_loc, None
        in
        let loc = Loc.btwn start_loc end_loc in
        env, (loc, Pattern.(Array Array.({
          elements;
          typeAnnotation;
        })))

    and pattern env restricted_error : env * Ast.Pattern.t =
      match Peek.token env with
      | T_LCURLY ->
          _object restricted_error env
      | T_LBRACKET ->
          _array restricted_error env
      | _ ->
          let env, id = Parse.identifier_with_type env restricted_error in
          env, (fst id, Pattern.Identifier id)
  end

  module JSX = struct
    let spread_attribute env =
      Eat.push_lex_mode env NORMAL_LEX;
      let start_loc = Peek.loc env in
      Expect.token env T_LCURLY;
      Expect.token env T_ELLIPSIS;
      let env, argument = Expression.assignment env in
      let end_loc = Peek.loc env in
      Expect.token env T_RCURLY;
      Eat.pop_lex_mode env;
      let loc = Loc.btwn start_loc end_loc in
      env, (loc, JSX.SpreadAttribute.({ argument; }))

    let expression_container env : env * (Loc.t * Ast.JSX.ExpressionContainer.t) =
      Eat.push_lex_mode env NORMAL_LEX;
      let start_loc = Peek.loc env in
      Expect.token env T_LCURLY;
      let env, expression = if Peek.token env = T_RCURLY
        then
          let empty_loc = Loc.btwn_exclusive start_loc (Peek.loc env) in
          env, JSX.ExpressionContainer.EmptyExpression empty_loc
        else
          let env, expr = Parse.expression env in
          env, JSX.ExpressionContainer.Expression expr
      in
      let end_loc = Peek.loc env in
      Expect.token env T_RCURLY;
      Eat.pop_lex_mode env;
      let loc = Loc.btwn start_loc end_loc in
      env, (loc, JSX.ExpressionContainer.({ expression; }))

    let identifier env =
      let loc = Peek.loc env in
      let name = Peek.value env in
      Expect.token env T_JSX_IDENTIFIER;
      loc, JSX.Identifier.({ name; })

    let name =
      let rec member_expression env member =
        match Peek.token env with
        | T_PERIOD ->
            let _object = JSX.MemberExpression.MemberExpression member in
            Expect.token env T_PERIOD;
            let property = identifier env in
            let loc = Loc.btwn (fst member) (fst property) in
            let member = loc, JSX.MemberExpression.({
              _object;
              property;
            }) in
            member_expression env member
        | _ -> member

      in fun env ->
        let name = identifier env in
        match Peek.token env with
        | T_COLON ->
            let namespace = name in
            Expect.token env T_COLON;
            let name = identifier env in
            let loc = Loc.btwn (fst namespace) (fst name) in
            JSX.NamespacedName (loc, JSX.NamespacedName.({
              namespace;
              name;
            }))
        | T_PERIOD ->
            let _object = JSX.MemberExpression.Identifier name in
            Expect.token env T_PERIOD;
            let property = identifier env in
            let loc = Loc.btwn (fst name) (fst property) in
            let member = loc, JSX.MemberExpression.({
              _object;
              property;
            }) in
            JSX.MemberExpression (member_expression env member)
        | _ -> JSX.Identifier name


    let attribute env : env * Ast.JSX.Attribute.t =
      let start_loc = Peek.loc env in
      let name = identifier env in
      let end_loc, name =
        if Peek.token env = T_COLON
        then begin
          Expect.token env T_COLON;
          let namespace = name in
          let name = identifier env in
          let loc = Loc.btwn (fst namespace) (fst name) in
          loc, JSX.Attribute.NamespacedName (loc, JSX.NamespacedName.({
            namespace;
            name;
          }))
        end else fst name, JSX.Attribute.Identifier name in
      let env, end_loc, value =
        if Peek.token env = T_ASSIGN
        then begin
          Expect.token env T_ASSIGN;
          match Peek.token env with
          | T_LCURLY ->
              let env, (loc, expression_container) = expression_container env in
              let env =
                let open JSX.ExpressionContainer in
                match expression_container.expression with
                | EmptyExpression _ ->
                    error env Error.JSXAttributeValueEmptyExpression;
                | _ -> env
              in
              let value =
                JSX.Attribute.ExpressionContainer (loc, expression_container) in
              env, loc, Some value
          | T_JSX_TEXT (loc, value, raw) as token ->
              Expect.token env token;
              let value = Ast.Literal.String value in
              let value = JSX.Attribute.Literal (loc, { Ast.Literal.value; raw;}) in
              env, loc, Some value
          | _ ->
              let env = error env Error.InvalidJSXAttributeValue in
              let loc = Peek.loc env in
              let raw = "" in
              let value = Ast.Literal.String "" in
              let value = JSX.Attribute.Literal (loc, { Ast.Literal.value; raw;}) in
              env, loc, Some value
        end else env, end_loc, None in
      let loc = Loc.btwn start_loc end_loc in
      env, (loc, JSX.Attribute.({ name; value; }))

      let opening_element_without_lt =
        let rec attributes env acc =
          match Peek.token env with
          | T_EOF
          | T_DIV
          | T_GREATER_THAN -> List.rev acc
          | T_LCURLY ->
              let env, attr = spread_attribute env in
              let attribute = JSX.Opening.SpreadAttribute attr in
              attributes env (attribute::acc)
          | _ ->
              let env, attr = attribute env in
              let attribute = JSX.Opening.Attribute attr in
              attributes env (attribute::acc)

        in fun env start_loc ->
          let name = name env in
          let attributes = attributes env [] in
          let selfClosing = Peek.token env = T_DIV in
          if selfClosing then Expect.token env T_DIV;
          let end_loc = Peek.loc env in
          Expect.token env T_GREATER_THAN;
          Eat.pop_lex_mode env;
          Loc.btwn start_loc end_loc, JSX.Opening.({
            name;
            selfClosing;
            attributes;
          })

      let closing_element_without_lt env start_loc : env * Ast.JSX.Closing.t =
        Expect.token env T_DIV;
        let name = name env in
        let end_loc = Peek.loc env in
        Expect.token env T_GREATER_THAN;
        (* We double pop to avoid going back to childmode and re-lexing the
         * lookahead *)
        Eat.double_pop_lex_mode env;
        env, (Loc.btwn start_loc end_loc, JSX.Closing.({
          name;
        }))

      type element_or_closing =
        | Closing of JSX.Closing.t
        | ChildElement of (Loc.t * JSX.element)


      let rec child env : env * Ast.JSX.child =
        match Peek.token env with
        | T_LCURLY ->
            let env, (loc, expression_container) = expression_container env in
            env, (loc, JSX.ExpressionContainer expression_container)
        | T_JSX_TEXT (loc, value, raw) as token ->
            Expect.token env token;
            env, (loc, JSX.Text { JSX.Text.value; raw; })
        | _ ->
            let env, (loc, element) = element env in
            env, (loc, JSX.Element element)

      and element_without_lt : env -> Loc.t -> env * (Loc.t * Ast.JSX.element) =
        let element_or_closing env : env * element_or_closing =
          Eat.push_lex_mode env JSX_TAG;
          let start_loc = Peek.loc env in
          Expect.token env T_LESS_THAN;
          match Peek.token env with
          | T_EOF
          | T_DIV ->
              let env, closing = closing_element_without_lt env start_loc in
              env, Closing closing
          | _ ->
              let env, element = element_without_lt env start_loc in
              env, ChildElement element

        in let rec children_and_closing env acc =
          match Peek.token env with
          | T_LESS_THAN -> (
              let env, thing = element_or_closing env in
              match thing with
              | Closing closingElement ->
                  env, List.rev acc, Some closingElement
              | ChildElement element ->
                  let element = fst element, JSX.Element (snd element) in
                  children_and_closing env (element::acc))
          | T_EOF ->
              let env = error_unexpected env in
              env, List.rev acc, None
          | _ ->
              let env, child = child env in
              children_and_closing env (child::acc)

        in let rec normalize name = JSX.(match name with
          | Identifier (_, { Identifier.name }) -> name
          | NamespacedName (_, { NamespacedName.namespace; name; }) ->
              (snd namespace).Identifier.name ^ ":" ^ (snd name).Identifier.name
          | MemberExpression (_, { MemberExpression._object; property; }) ->
              let _object = match _object with
              | MemberExpression.Identifier id -> (snd id).Identifier.name
              | MemberExpression.MemberExpression e -> normalize (JSX.MemberExpression e) in
              _object ^ "." ^ (snd property).Identifier.name
        )

        in fun env start_loc ->
          let openingElement = opening_element_without_lt env start_loc in
          let env, children, closingElement =
            if (snd openingElement).JSX.Opening.selfClosing
            then env, [], None
            else begin
              Eat.push_lex_mode env JSX_CHILD;
              children_and_closing env []
            end in
          let env, end_loc = match closingElement with
          | Some (loc, { JSX.Closing.name }) ->
              let opening_name = normalize (snd openingElement).JSX.Opening.name in
              let env = if normalize name <> opening_name
                then error env (Error.ExpectedJSXClosingTag opening_name)
                else env in
              env, loc
          | _ -> env, fst openingElement in
          let loc = Loc.btwn (fst openingElement) end_loc in
          let expr = loc, JSX.({openingElement; closingElement; children;}) in
          env, expr

      and element env : env * (Loc.t * Ast.JSX.element) =
        let start_loc = Peek.loc env in
        Eat.push_lex_mode env JSX_TAG;
        Expect.token env T_LESS_THAN;
        element_without_lt env start_loc
  end

  let rec program env =
    let env, stmts = module_body_with_directives env (fun _ -> false) in
    Expect.token env T_EOF;
    let loc = match stmts with
    | [] -> Loc.from_lb (source env) (lb env)
    | _ -> Loc.btwn (fst (List.hd stmts)) (fst (List.hd (List.rev stmts))) in
    let comments = List.rev (comments env) in
    env, (loc, stmts, comments)

  and directives : env -> ('a -> bool) -> (env -> env * Ast.Statement.t) -> env * Ast.Statement.t list =
      let check env (loc, token) : env =
        match token with
        | T_STRING (_, _, _, octal) ->
            if octal
              then strict_error_at env (loc, Error.StrictOctalLiteral)
              else env
        | _ -> failwith ("Nooo: "^(token_to_string token)^"\n")

      in let rec statement_list env term_fn item_fn (string_tokens, stmts) =
        match Peek.token env with
        | T_EOF -> env, string_tokens, stmts
        | t when term_fn t -> env, string_tokens, stmts
        | _ ->
            let string_token = Peek.loc env, Peek.token env in
            let env, possible_directive = item_fn env in
            let stmts = possible_directive::stmts in
            (match possible_directive with
            | _, Ast.Statement.Expression {
                Ast.Statement.Expression.expression = loc, Ast.Expression.Literal {
                  Ast.Literal.value = Ast.Literal.String str;
                  _;
                }
              } ->
                (* 14.1.1 says that it has to be "use strict" without any
                  * escapes, so "use\x20strict" is disallowed. We could in theory
                  * keep the raw string around, but that's a pain. This is a hack
                  * that actually seems to work pretty well (make sure the string
                  * has the right length)
                  *)
                let len = Loc.(loc._end.column - loc.start.column) in
                let strict = (strict env) || (str = "use strict" && len = 12) in
                let string_tokens = string_token::string_tokens in
                statement_list
                  (env |> with_strict strict)
                  term_fn
                  item_fn
                  (string_tokens, stmts)
            | _ ->
                env, string_tokens, stmts)

      in fun env term_fn item_fn ->
        let env, string_tokens, stmts = statement_list env term_fn item_fn ([], []) in
        let env = List.fold_left check env (List.rev string_tokens) in
        env, stmts

  (* 15.2 *)
  and module_item env : env * Ast.Statement.t =
    let decorators = Object.decorator_list env in
    match Peek.token env with
    | T_EXPORT -> Statement.export_declaration env decorators
    | T_IMPORT ->
        let env = error_on_decorators env decorators in
        Statement.import_declaration env
    | T_DECLARE when Peek.token ~i:1 env = T_EXPORT ->
        let env = error_on_decorators env decorators in
        Statement.declare_export_declaration env
    | _ -> statement_list_item env ~decorators

  and module_body_with_directives env term_fn : env * Ast.Statement.t list =
    let env, directives = directives env term_fn module_item in
    let env, stmts = module_body ~term_fn env in
    (* Prepend the directives *)
    env, List.fold_left (fun acc stmt -> stmt::acc) stmts directives

  and module_body : term_fn:('a -> bool) -> env -> env * Ast.Statement.t list =
    let rec module_item_list env term_fn acc =
      match Peek.token env with
      | T_EOF -> env, List.rev acc
      | t when term_fn t -> env, List.rev acc
      | _ ->
        let env, item = module_item env in
        module_item_list env term_fn (item::acc)

    in fun ~term_fn env ->
      module_item_list env term_fn []

  and statement_list_with_directives ~term_fn env : env * Ast.Statement.t list * bool =
    let env, directives = directives env term_fn statement_list_item in
    let env, stmts = statement_list ~term_fn env in
    (* Prepend the directives *)
    let stmts = List.fold_left (fun acc stmt -> stmt::acc) stmts directives in
    env, stmts, (strict env)

  and statement_list : term_fn: (token -> bool) -> env -> env * Ast.Statement.t list =
    let rec statements env term_fn acc =
      match Peek.token env with
      | T_EOF -> env, List.rev acc
      | t when term_fn t -> env, List.rev acc
      | _ ->
        let env, stmt = statement_list_item env in
        statements env term_fn (stmt::acc)

    in fun ~term_fn env -> statements env term_fn []


  and statement_list_item ?(decorators=[]) env : env * Ast.Statement.t =
    let env = if not (Peek._class env)
      then error_on_decorators env decorators
      else env in
    Statement.(match Peek.token env with
    (* Remember kids, these look like statements but they're not
      * statements... (see section 13) *)
    | T_LET -> _let env
    | T_CONST -> var_or_const env
    | _ when Peek._function env -> Declaration._function env
    | _ when Peek._class env -> class_declaration env decorators
    | T_INTERFACE -> interface env
    | T_DECLARE -> declare env
    | T_TYPE -> type_alias env
    | _ -> statement env)

  and statement env : env * Ast.Statement.t =
    Statement.(match Peek.token env with
    | T_EOF ->
        let env = error_unexpected env in
        env, (Peek.loc env, Ast.Statement.Empty)
    | T_SEMICOLON -> empty env
    | T_LCURLY -> block env
    | T_VAR -> var_or_const env
    | T_BREAK -> break env
    | T_CONTINUE -> continue env
    | T_DEBUGGER -> debugger env
    | T_DO -> do_while env
    | T_FOR -> _for env
    | T_IF -> _if env
    | T_RETURN -> return env
    | T_SWITCH -> switch env
    | T_THROW -> throw env
    | T_TRY -> _try env
    | T_WHILE -> _while env
    | T_WITH -> _with env
    | _ when Peek.identifier env -> maybe_labeled env
    (* If we see an else then it's definitely an error, but we can probably
     * assume that this is a malformed if statement that is missing the if *)
    | T_ELSE -> _if env
    (* There are a bunch of tokens that aren't the start of any valid
     * statement. We list them here in order to skip over them, rather than
     * getting stuck *)
    | T_COLON
    | T_RPAREN
    | T_RCURLY
    | T_RBRACKET
    | T_COMMA
    | T_PERIOD
    | T_ARROW
    | T_IN
    | T_INSTANCEOF
    | T_CATCH
    | T_FINALLY
    | T_CASE
    | T_DEFAULT
    | T_EXTENDS
    | T_STATIC
    | T_IMPORT (* TODO *)
    | T_EXPORT (* TODO *)
    | T_ELLIPSIS ->
        let env = error_unexpected env in
        Eat.token env;
        statement env
    | _ -> expression env)

  and expression env =
    let env, expr = Expression.assignment env in
    match Peek.token env with
    | T_COMMA -> Expression.sequence env [expr]
    | _ ->
        env, expr

  and assignment = Expression.assignment
  and object_initializer = Object._initializer
  and object_key = Object.key
  and class_declaration = Object.class_declaration
  and class_expression = Object.class_expression
  and array_initializer = Expression.array_initializer

  and is_assignable_lhs = Expression.is_assignable_lhs

  and identifier ?restricted_error env : env * Ast.Identifier.t =
    let loc = Peek.loc env in
    let name = Peek.value env in
    (match Peek.token env with
    | T_LET ->
    (* So "let" is disallowed as an identifier in a few situations. 11.6.2.1
     * lists them out. It is always disallowed in strict mode *)
      let env =
        if strict env then strict_error env Error.StrictReservedWord
        else if no_let env then error env (Error.UnexpectedToken name)
        else env
      in
      Eat.token env
    | _ when is_strict_reserved name ->
      let env = strict_error env Error.StrictReservedWord in
      Eat.token env
    | T_DECLARE
    | T_OF
    | T_ASYNC
    | T_AWAIT
    | T_TYPE as t ->
        (* These aren't real identifiers *)
        Expect.token env t
    | _ -> Expect.token env T_IDENTIFIER);
    let env = match restricted_error with
    | Some err when is_restricted name -> strict_error_at env (loc, err)
    | _ -> env
    in
    env, (loc, Identifier.({
      name;
      typeAnnotation = None;
      optional = false;
    }))

  and identifier_or_reserved_keyword = Expression.identifier_or_reserved_keyword

  and identifier_with_type env restricted_error : env * Ast.Identifier.t =
    let env, (loc, id) = identifier ~restricted_error env in
    let loc, id =
      if Peek.token env = T_PLING
      then begin
        let env = if not (should_parse_types env)
          then error env Error.UnexpectedTypeAnnotation
          else env in
        let loc = Loc.btwn loc (Peek.loc env) in
        Expect.token env T_PLING;
        loc, { id with Identifier.optional = true; }
      end else (loc, id) in
    if Peek.token env = T_COLON
    then begin
      let typeAnnotation = Type.annotation env in
      let loc = Loc.btwn loc (fst typeAnnotation) in
      let typeAnnotation = Some typeAnnotation in
      env, Identifier.(loc, { id with typeAnnotation; })
    end else env, (loc, id)

  and block_body env : env * (Loc.t * Ast.Statement.Block.t) =
    let start_loc = Peek.loc env in
    Expect.token env T_LCURLY;
    let term_fn = fun t -> t = T_RCURLY in
    let env, body = statement_list ~term_fn env in
    let end_loc = Peek.loc env in
    Expect.token env T_RCURLY;
    env, (Loc.btwn start_loc end_loc, { Ast.Statement.Block.body; })

  and function_block_body env : env * Loc.t * Ast.Statement.Block.t * bool =
    let start_loc = Peek.loc env in
    Expect.token env T_LCURLY;
    let term_fn = fun t -> t = T_RCURLY in
    let env, body, strict = statement_list_with_directives ~term_fn env in
    let end_loc = Peek.loc env in
    Expect.token env T_RCURLY;
    env, Loc.btwn start_loc end_loc, { Ast.Statement.Block.body; }, strict

  and jsx_element = JSX.element

  and pattern = Pattern.pattern
  and pattern_from_expr = Pattern.from_expr
end

(*****************************************************************************)
(* Entry points *)
(*****************************************************************************)
let mk_parse_env ?(token_sink=None) ?(parse_options=None) filename content =
  let lb = Lexing.from_string content in
  (match filename with
    | None
    | Some Loc.Builtins -> ()
    | Some Loc.LibFile fn
    | Some Loc.SourceFile fn
    | Some Loc.JsonFile fn ->
      lb.Lexing.lex_curr_p <- {
        lb.Lexing.lex_curr_p with Lexing.pos_fname = fn
      });
  init_env ~token_sink ~parse_options filename lb

let do_parse env (parser: env -> env * 'a) (fail: bool) : 'a * (Loc.t * Error.t) list =
  let env, ast = parser env in
  let error_list = filter_duplicate_errors (errors env) in
  if fail && error_list <> []
  then raise (Error.Error error_list);
  ast, error_list

let parse_program fail ?(token_sink=None) ?(parse_options=None) filename content =
  let env = mk_parse_env ~token_sink ~parse_options filename content in
  do_parse env Parse.program fail

let program ?(fail=true) ?(token_sink=None) ?(parse_options=None) content =
  parse_program fail ~token_sink ~parse_options None content

let program_file ?(fail=true) ?(token_sink=None) ?(parse_options=None) content filename =
  parse_program fail ~token_sink ~parse_options filename content

(* even if fail=false, still raises an error on a totally invalid token, since
   there's no legitimate fallback. *)
let json_file ?(fail=true) ?(token_sink=None) ?(parse_options=None) content filename =
  let env = mk_parse_env ~token_sink ~parse_options filename content in
  match Peek.token env with
  | T_LBRACKET
  | T_LCURLY
  | T_STRING _
  | T_NUMBER _
  | T_TRUE
  | T_FALSE
  | T_NULL ->
    do_parse env Parse.expression fail
  | T_MINUS ->
    (match Peek.token ~i:1 env with
    | T_NUMBER _ ->
      do_parse env Parse.expression fail
    | _ ->
      let env = error_unexpected env in
      raise (Error.Error (errors env)))
  | _ ->
    let env = error_unexpected env in
    raise (Error.Error (errors env))
