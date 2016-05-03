module Ops :
  sig
    val clear : unit -> Reason_js.reason list
    val push : Reason_js.reason -> unit
    val pop : unit -> unit
    val peek : unit -> Reason_js.reason option
    val get : unit -> Reason_js.reason list
    val set : Reason_js.reason list -> unit
  end

exception SpeculativeError of Errors_js.error
val set_speculative : unit -> unit
val restore_speculative : unit -> unit
val speculation_depth : unit -> int

val mk_info : Reason_js.reason -> string list -> Errors_js.info
val info_of_reason : Reason_js.reason -> Errors_js.info
val add_warning :
  Context.t -> ?extra:Errors_js.info_tree list -> Errors_js.info -> unit
val add_error :
  Context.t -> ?extra:Errors_js.info_tree list -> Errors_js.info -> unit
val add_extended_error :
  Context.t -> ?extra:Errors_js.info_tree list -> Errors_js.info list -> unit
val add_internal_error :
  Context.t -> ?extra:Errors_js.info_tree list -> Errors_js.info -> unit
val flow_err :
  Context.t ->
  Trace.t ->
  string -> ?extra:Errors_js.info_tree list -> Type.t -> Type.use_t -> unit
val flow_err_use_t :
  Context.t ->
  Trace.t ->
  string -> ?extra:Errors_js.info_tree list -> Type.t -> Type.t -> unit
val flow_err_reasons :
  Context.t ->
  Trace.t ->
  string ->
  ?extra:Errors_js.info_tree list -> Reason_js.reason * Reason_js.reason -> unit
val flow_err_prop_not_found :
  Context.t -> Trace.t -> Reason_js.reason * Reason_js.reason -> unit
