(*********************************************************************************)
(*                OCaml-lru-cache                                                *)
(*                                                                               *)
(*    Copyright (C) 2016 Institut National de Recherche en Informatique          *)
(*    et en Automatique. All rights reserved.                                    *)
(*                                                                               *)
(*    This program is free software; you can redistribute it and/or modify       *)
(*    it under the terms of the BSD3 License.                                    *)
(*                                                                               *)
(*    This program is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of             *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                       *)
(*                                                                               *)
(*    Contact: Maxence.Guesdon@inria.fr                                          *)
(*                                                                               *)
(*                                                                               *)
(*********************************************************************************)

open Core

module type Key = sig
  include Hashable.S

  (*val equal : t -> t -> bool
  val sexp_of_t : t -> Sexp.t
    val t_of_sexp : Sexp.t -> t*)
end

module type S =
  sig
    type key
    type 'a t

    val init : size: int -> key -> 'a t
    val get : 'a t ->
      key -> (key -> 'a) -> 'a
  end

module Make_with_monad (K:Key) : (S with type key = K.t) =
  struct
    type key = K.t

    module M = K.Table
    type 'a v = { v: 'a; pos: int }

    type 'a t =
      { map: ('a v) M.t ;
        keys: key array ;
        size: int ;
        mutable least_recent: int;
      }

    let init ~size witness =
      { map = K.Table.create () ;
        keys = Array.init size ~f:(fun _ -> witness) ;
        size = size;
        least_recent = 0;
      }

    let remove_last t =
      let least_recent = t.least_recent in
      let k = t.keys.(least_recent) in
      begin match M.find t.map k with
        | None -> ()
        | Some v ->
          if v.pos = t.least_recent then
            M.remove t.map k
          else
            ()
      end

    let insert t key v =
      remove_last t;
      t.keys.(t.least_recent) <- key ;
      M.set t.map ~key ~data:({ v = v ; pos = t.least_recent });
      t.least_recent <- ((t.least_recent + 1) mod t.size);
      ()

    let get t k f =
      match M.find t.map k with
      | None ->
        let v = f k in
        insert t k v; v
      | Some { v = v ; pos = _ } ->
        Consts.utilization := !Consts.utilization + 1;
        insert t k v;
        v

  end

module Make (K:Key) = Make_with_monad(K)
