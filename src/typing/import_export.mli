(**
 * Copyright (c) 2013-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the "flow" directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 *
 *)

val mk_module_t : Context.t -> Reason_js.reason -> Type.t
val mk_commonjs_module_t :
  Context.t -> Reason_js.reason -> Reason_js.reason -> Type.t -> Type.t
val get_module_t : Context.t -> SMap.key -> Reason_js.reason -> Type.t
val require : Context.t -> SMap.key -> Loc.t -> Type.t
val import :
  ?reason:Reason_js.reason -> Context.t -> SMap.key -> Loc.t -> Type.t
val import_ns : Context.t -> Reason_js.reason -> SMap.key -> Loc.t -> Type.t
val exports : Context.t -> Type.t
val set_module_t : Context.t -> Reason_js.reason -> (Type.t -> unit) -> unit
val mark_exports_type :
  Context.t -> Reason_js.reason -> Context.module_exports_type -> unit
val nameify_default_export_decl :
  Loc.t * Spider_monkey_ast.Statement.t' ->
  Loc.t * Spider_monkey_ast.Statement.t'
val warn_or_ignore_export_star_as : Context.t -> (Loc.t * 'a) option -> unit
val get_module_exports : Context.t -> Reason_js.reason -> Type.t
val set_module_exports : Context.t -> Reason_js.reason -> Type.t -> unit
