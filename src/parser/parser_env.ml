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
module Ast = Spider_monkey_ast
open Ast
module Error = Parse_error
module SSet = Set.Make(String)
module SMap = Map.Make(String)

(* READ THIS BEFORE YOU MODIFY:
 *
 * The current implementation for lookahead beyond a single token is
 * inefficient. If you believe you need to increase this constant, do one of the
 * following:
 * - Find another way
 * - Benchmark your change and provide convincing evidence that it doesn't
 *   actually have a significant perf impact.
 * - Refactor this to memoize all requested lookahead, so we aren't lexing the
 *   same token multiple times.
 *)
let maximum_lookahead = 2

type lex_mode =
  | NORMAL_LEX
  | TYPE_LEX
  | JSX_TAG
  | JSX_CHILD

let mode_to_string = function
  | NORMAL_LEX -> "NORMAL"
  | TYPE_LEX -> "TYPE"
  | JSX_TAG -> "JSX TAG"
  | JSX_CHILD -> "JSX CHILD"

let lex lex_env = function
  | NORMAL_LEX -> token lex_env
  | TYPE_LEX -> type_token lex_env
  | JSX_TAG -> lex_jsx_tag lex_env
  | JSX_CHILD -> lex_jsx_child lex_env

module Lookahead : sig
  type t
  val create : Lexing.lexbuf -> lex_env -> lex_mode -> t
  val peek : t -> int -> lex_result
  val junk : t -> unit
end = struct
  type t = {
    mutable la_results    : lex_result option array;
    mutable la_num_lexed  : int;
    la_lex_mode           : lex_mode;
    mutable la_lex_env    : lex_env;
  }

  let create lb lex_env mode =
    (* copy all the mutable things so that we have a distinct lexing environment
     * that does not interfere with ordinary lexer operations *)
    (* lex_buffer has type bytes, which is itself mutable, but the lexer
     * promises not to change it so a shallow copy should be fine *)
    (* I don't know how to do a copy without an update *)
    let lb = Lexing.({ lb with lex_buffer = lb.lex_buffer }) in
    let lex_env = { lex_env with
      lex_lb = lb;
      lex_state = ref !(lex_env.lex_state)
    } in
    {
      la_results = [||];
      la_num_lexed = 0;
      la_lex_mode = mode;
      la_lex_env = lex_env;
    }

  let next_power_of_two n =
    let rec f i =
      if i >= n then
        i
      else
        f (i * 2) in
    f 1

  (* resize the tokens array to have at least n elements *)
  let grow t n =
    if Array.length t.la_results < n then begin
      let new_size = next_power_of_two n in
      let filler i =
        if i < Array.length t.la_results then
          t.la_results.(i)
        else
          None in
      let new_arr = Array.init new_size filler in
      t.la_results <- new_arr
    end

  (* precondition: there is enough room in t.la_results for the result *)
  let lex t =
    let lex_env, lex_result = lex t.la_lex_env t.la_lex_mode in
    t.la_lex_env <- lex_env;
    t.la_results.(t.la_num_lexed) <- Some lex_result;
    t.la_num_lexed <- t.la_num_lexed + 1

  let lex_until t i =
    grow t (i + 1);
    while t.la_num_lexed <= i do
      lex t
    done

  let peek t i =
    lex_until t i;
    match t.la_results.(i) with
      | Some result -> result
      (* only happens if there is a defect in the lookahead module *)
      | None -> failwith "Lookahead.peek failed"

  (* Throws away the first peeked-at token, shifting any subsequent tokens up *)
  let junk t =
    lex_until t 1;
    if t.la_num_lexed > 1 then
      Array.blit t.la_results 1 t.la_results 0 (t.la_num_lexed - 1);
    t.la_results.(t.la_num_lexed - 1) <- None;
    t.la_num_lexed <- t.la_num_lexed - 1;
end

type token_sink_result = {
  token_loc: Loc.t;
  token: Lexer_flow.token;
  token_context: lex_mode;
  token_value: string;
}

type parse_options = {
  esproposal_class_instance_fields: bool;
  esproposal_class_static_fields: bool;
  esproposal_decorators: bool;
  esproposal_export_star_as: bool;
  types: bool;
  use_strict: bool;
}
let default_parse_options = {
  esproposal_class_instance_fields = false;
  esproposal_class_static_fields = false;
  esproposal_decorators = false;
  esproposal_export_star_as = false;
  types = true;
  use_strict = false;
}

type env = {
  errors            : (Loc.t * Error.t) list ref;
  comments          : Comment.t list ref;
  labels            : SSet.t;
  exports           : SSet.t ref;
  (* the lex buffer in the state after a single lookahead *)
  lb                : Lexing.lexbuf;
  last              : (lex_env * lex_result) option ref;
  priority          : int;
  strict            : bool;
  in_export         : bool;
  in_loop           : bool;
  in_switch         : bool;
  in_function       : bool;
  no_in             : bool;
  no_call           : bool;
  no_let            : bool;
  allow_yield       : bool;
  allow_await       : bool;
  error_callback    : error_callback;
  lex_mode_stack    : lex_mode list ref;
  (* lex_env is the lex_env after the single lookahead has been lexed *)
  lex_env           : lex_env ref;
  (* This needs to be cleared whenever we advance. *)
  lookahead         : Lookahead.t option ref;
  token_sink        : (token_sink_result -> unit) option ref;
  parse_options     : parse_options;
  source            : Loc.filename option;
}
and error_callback' = (env -> Error.t -> unit) option
and error_callback = error_callback'

(* constructor *)
let init_env ?(token_sink=None) ?(parse_options=None) source lb =
  let parse_options =
    match parse_options with
    | Some opts -> opts
    | None -> default_parse_options
  in
  let enable_types_in_comments = parse_options.types in
  let lex_env = new_lex_env source lb ~enable_types_in_comments in
  {
    errors            = ref [];
    comments          = ref [];
    labels            = SSet.empty;
    exports           = ref SSet.empty;
    lb                = lb;
    last              = ref None;
    priority          = 0;
    strict            = parse_options.use_strict;
    in_export         = false;
    in_loop           = false;
    in_switch         = false;
    in_function       = false;
    no_in             = false;
    no_call           = false;
    no_let            = false;
    allow_yield       = true;
    allow_await       = false;
    error_callback    = None;
    lex_mode_stack    = ref [NORMAL_LEX];
    lex_env           = ref lex_env;
    lookahead         = ref None;
    token_sink        = ref token_sink;
    parse_options;
    source;
  }

(* getters: *)
let strict env = env.strict
let lb env = env.lb
let lex_mode env = List.hd !(env.lex_mode_stack)
let lex_env env = !(env.lex_env)
let in_export env = env.in_export
let comments env = !(env.comments)
let labels env = env.labels
let in_loop env = env.in_loop
let in_switch env = env.in_switch
let in_function env = env.in_function
let allow_yield env = env.allow_yield
let allow_await env = env.allow_await
let no_in env = env.no_in
let no_call env = env.no_call
let no_let env = env.no_let
let errors env = !(env.errors)
let parse_options env = env.parse_options
let source env = env.source
let should_parse_types env = env.parse_options.types

(* mutators: *)
let error_at env (loc, e) =
  env.errors := (loc, e) :: !(env.errors);
  begin match env.error_callback with
  | None -> ()
  | Some callback -> callback env e
  end;
  env
let comment_list env =
  List.iter (fun c -> env.comments := c :: !(env.comments))
let set_lex_env env lex_env =
  env.lookahead := None;
  env.lex_env := lex_env
let record_export env (loc, export_name) =
  let exports = !(env.exports) in
  if SSet.mem export_name exports
  then error_at env (loc, Error.DuplicateExport export_name)
  else begin
    env.exports := SSet.add export_name !(env.exports);
    env
  end

(* lookahead: *)
let lookahead ?(i=0) env =
  assert (i < maximum_lookahead);
  let lookahead = match !(env.lookahead) with
    | Some l -> l
    | None -> begin
        let l = Lookahead.create (lb env) (lex_env env) (lex_mode env) in
        env.lookahead := Some l;
        l
      end in
  Lookahead.peek lookahead i

(* functional operations: *)
let with_strict strict env = { env with strict }
let with_in_function in_function env = { env with in_function }
let with_allow_yield allow_yield env = { env with allow_yield }
let with_allow_await allow_await env = { env with allow_await }
let with_no_let no_let env = { env with no_let }
let with_in_loop in_loop env = { env with in_loop }
let with_no_in no_in env = { env with no_in }
let with_in_switch in_switch env = { env with in_switch }
let with_in_export in_export env = { env with in_export }
let with_no_call no_call env = { env with no_call }
let with_error_callback error_callback env =
  { env with error_callback = Some error_callback }, env.error_callback
let without_error_callback env =
  { env with error_callback = None }, env.error_callback
let restore_error_callback error_callback env =
  { env with error_callback }

(* other helper functions: *)
let error_list env errors = List.fold_left error_at env errors
let last_loc env = match !(env.last) with
  | None -> None
  | Some (_, result) -> Some result.lex_loc

let advance env (lex_env, lex_result) =
  (* If there's a token_sink, emit the lexed token before moving forward *)
  (match !(env.token_sink) with
    | None -> ()
    | Some token_sink ->
        let {lex_loc; lex_token; lex_value; _;} = lex_result in
        token_sink {
          token_loc=lex_loc;
          token=lex_token;
          (**
           * The lex mode is useful because it gives context to some
           * context-sensitive tokens.
           *
           * Some examples of such tokens include:
           *
           * `=>` - Part of an arrow function? or part of a type annotation?
           * `<`  - A less-than? Or an opening to a JSX element?
           * ...etc...
           *)
          token_context=(lex_mode env);
          token_value=lex_value
        }
  );

  (* commit the result's lexbuf state *)
  env.lb.Lexing.lex_abs_pos <- lex_result.lex_lb_abs_pos;
  env.lb.Lexing.lex_start_pos <- lex_result.lex_lb_start_pos;
  env.lb.Lexing.lex_curr_pos <- lex_result.lex_lb_curr_pos;
  env.lb.Lexing.lex_last_pos <- lex_result.lex_lb_last_pos;
  env.lb.Lexing.lex_last_action <- lex_result.lex_lb_last_action;
  env.lb.Lexing.lex_eof_reached <- lex_result.lex_lb_eof_reached;
  env.lb.Lexing.lex_mem <- lex_result.lex_lb_mem;
  env.lb.Lexing.lex_start_p <- lex_result.lex_lb_start_p;
  env.lb.Lexing.lex_curr_p <- lex_result.lex_lb_curr_p;

  env.lex_env := { lex_env with
    lex_in_comment_syntax = lex_result.lex_result_in_comment_syntax
  };

  let env = error_list env lex_result.lex_errors in
  comment_list env lex_result.lex_comments;
  env.last := Some (lex_env, lex_result);
  match !(env.lookahead) with
  | Some la -> Lookahead.junk la
  | None -> ()

let push_lex_mode env mode =
  env.lex_mode_stack := mode :: !(env.lex_mode_stack);
  env.lookahead := None

let pop_lex_mode env =
  let new_stack = match !(env.lex_mode_stack) with
  | _mode::stack -> stack
  | _ -> failwith "Popping lex mode from empty stack" in
  env.lex_mode_stack := new_stack;
  env.lookahead := None

let double_pop_lex_mode env =
  let new_stack = match !(env.lex_mode_stack) with
  | _::_::stack -> stack
  | _ -> failwith "Popping lex mode from empty stack" in
  env.lex_mode_stack := new_stack;
  env.lookahead := None

let add_label env label = { env with labels = SSet.add label env.labels }
let enter_function env ~async ~generator = { env with
    in_function = true;
    in_loop = false;
    in_switch = false;
    labels = SSet.empty;
    allow_await = async;
    allow_yield = generator;
  }
let leave_function ~prev_env env = { env with
    in_function = prev_env.in_function;
    in_loop = prev_env.in_loop;
    in_switch = prev_env.in_switch;
    labels = prev_env.labels;
    allow_await = prev_env.allow_await;
    allow_yield = prev_env.allow_yield;
  }

(* This module allows you to try parsing and rollback if you need. This is not
 * cheap and its usage is strongly discouraged *)
module Try = struct
  type 'a parse_result =
    | ParsedSuccessfully of 'a
    | FailedToParse

  exception Rollback

  type saved_state = {
    saved_errors         : (Loc.t * Error.t) list;
    saved_comments       : Ast.Comment.t list;
    saved_lb             : Lexing.lexbuf;
    saved_last           : (lex_env * lex_result) option;
    saved_lex_mode_stack : lex_mode list;
    saved_lex_env        : lex_env;
    token_buffer         : ((token_sink_result -> unit) * token_sink_result Queue.t) option;
  }

  let save_state env =
    let token_buffer =
      match !(env.token_sink) with
      | None -> None
      | Some orig_token_sink ->
          let buffer = Queue.create () in
          env.token_sink := Some(fun token_data ->
            Queue.add token_data buffer
          );
          Some(orig_token_sink, buffer)
    in
    {
      saved_errors         = !(env.errors);
      saved_comments       = !(env.comments);
      saved_lb             =
        Lexing.({env.lb with lex_abs_pos=env.lb.lex_abs_pos});
      saved_last           = !(env.last);
      saved_lex_mode_stack = !(env.lex_mode_stack);
      saved_lex_env        = !(env.lex_env);
      token_buffer;
    }

  let reset_token_sink ~flush env token_buffer_info =
    match token_buffer_info with
    | None -> ()
    | Some(orig_token_sink, token_buffer) ->
        env.token_sink := Some orig_token_sink;
        if flush then Queue.iter orig_token_sink token_buffer

  let rollback_state env saved_state =
    reset_token_sink ~flush:false env saved_state.token_buffer;
    env.errors := saved_state.saved_errors;
    env.comments := saved_state.saved_comments;
    env.last := saved_state.saved_last;
    env.lex_mode_stack := saved_state.saved_lex_mode_stack;
    env.lex_env := saved_state.saved_lex_env;
    env.lookahead := None;

    Lexing.(begin
      env.lb.lex_buffer <- saved_state.saved_lb.lex_buffer;
      env.lb.lex_buffer_len <- saved_state.saved_lb.lex_buffer_len;
      env.lb.lex_abs_pos <- saved_state.saved_lb.lex_abs_pos;
      env.lb.lex_start_pos <- saved_state.saved_lb.lex_start_pos;
      env.lb.lex_curr_pos <- saved_state.saved_lb.lex_curr_pos;
      env.lb.lex_last_pos <- saved_state.saved_lb.lex_last_pos;
      env.lb.lex_last_action <- saved_state.saved_lb.lex_last_action;
      env.lb.lex_eof_reached <- saved_state.saved_lb.lex_eof_reached;
      env.lb.lex_mem <- saved_state.saved_lb.lex_mem;
      env.lb.lex_start_p <- saved_state.saved_lb.lex_start_p;
      env.lb.lex_curr_p <- saved_state.saved_lb.lex_curr_p;
    end);

    FailedToParse

  let success env saved_state result =
    reset_token_sink ~flush:true env saved_state.token_buffer;
    ParsedSuccessfully result

  let to_parse env parse =
    let saved_state = save_state env in
    try success env saved_state (parse env)
    with Rollback -> rollback_state env saved_state
end
