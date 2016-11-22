(**
 * Copyright (c) 2013-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the "flow" directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 *
 *)

type key = string list
type kind =
  | Lib
  | Source
  | Json
  | Resource
  | Unknown
type 'a t =
  | File of kind * 'a
  | Dir of 'a t SMap.t
  | Symlink of key

exception File_as_dir
  (* trying to add a file to the tree when there's a dir there already *)

exception Dir_as_file
  (* trying to add a dir to the tree when there's a file there already *)

let empty = Dir (SMap.empty)

let add ((kind, path): kind * key) (v: 'a) (tree: 'a t) : 'a t  =
  let rec walk = function
  | [], File _ -> File (kind, v)
  | [], Symlink _ -> raise File_as_dir (* TODO: follow symlink? *)
  | [], Dir _ -> raise File_as_dir
  | _::_, File _ -> raise Dir_as_file
  | _::_, Symlink _ -> raise Dir_as_file (* TODO: follow symlink? *)
  | x::rest, Dir map ->
      let subtree =
        try SMap.find_unsafe x map
        with Not_found ->
          if rest = [] then File (kind, v) else Dir (SMap.empty)
      in
      let tree' = walk (rest, subtree) in
      Dir (SMap.add x tree' map)
  in
  walk (path, tree)

let rec mem ((kind, path): kind * key) (tree: 'a t) =
  match (path, tree) with
  | _, Symlink link -> mem (kind, link @ path) tree
  | [], Dir _ -> false
  | [], File (kind', _) -> kind = kind'
  | _::_, File _ -> false
  | x::rest, Dir map ->
    try mem (kind, rest) (SMap.find x map) with Not_found -> false

let find (path: key) (tree: 'a t) : bool =
  let rec walk = function
  | path', Symlink link -> walk (link @ path', tree)
  | [], File (_, v) -> v
  | [], _ -> raise Not_found
  | _::_, File _ -> raise File_as_dir
  | x::rest, Dir map -> walk (rest, SMap.find_unsafe x map)
  in
  walk (path, tree)

let fold (f: (kind * key) -> 'a -> 'b -> 'b) (tree: 'a t) (acc: 'b) =
  let rec walk revp tree acc = match tree with
    | Dir map ->
        SMap.fold (fun x -> walk (x::revp)) map acc
    | Symlink _ -> acc (* points elsewhere in the tree so will be visited *)
    | File (kind, v) ->
        f (kind, List.rev revp) v acc
  in
  walk [] tree acc

let exists (f: (kind * key) -> 'a -> bool) (tree: 'a t) : bool =
  let rec walk revp = function
  | Dir map ->
      SMap.exists (fun x -> walk (x::revp)) map
  | Symlink _ -> false (* TODO *)
  | File (kind, v) ->
      f (kind, List.rev revp) v
  in
  walk [] tree

let bindings : 'a t -> ((kind * key) * 'a) list =
  let rec walk acc revp = function
  | Symlink _ -> acc
  | File (kind, v) -> ((kind, List.rev revp), v)::acc
  | Dir map ->
      SMap.fold (fun x tree acc ->
        walk acc (x::revp) tree
      ) map acc
  in
  fun (tree: 'a t) -> walk [] [] tree
