open Core

type t =
  | Named of Id.t
  | Arrow of t * t
  | Tuple of t list
  | Mu of Id.t * t
  | Variant of (Id.t * t) list
[@@deriving bin_io, eq, hash, ord, sexp, show]

let mk_named (i : Id.t) : t =
  Named i

let mk_arrow (t1:t) (t2:t) : t =
  Arrow (t1,t2)

let mk_mu (i:Id.t) (t:t) : t =
  if equal t (mk_named i) then
    failwith "cannot do infinite loop";
  Mu (i,t)

let fold (type a)
         ~(name_f : Id.t -> a)
         ~(arr_f : a -> a -> a)
         ~(tuple_f : a list -> a)
         ~(mu_f : Id.t -> a -> a)
         ~(variant_f : (Id.t * a) list -> a)
         (e : t)
         : a =
  let rec fold_internal (e : t) : a =
    match e with
      | Named v -> name_f v
      | Arrow (e1,e2) -> arr_f (fold_internal e1) (fold_internal e2)
      | Tuple es -> tuple_f (List.map ~f:fold_internal es)
      | Mu (i,e) -> mu_f i (fold_internal e)
      | Variant variants ->
        variant_f (List.map ~f:(fun (i,t) -> (i,fold_internal t)) variants)
  in fold_internal e

let arr_apply (type a) ~(f : t -> t -> a) (ty : t) : a option =
  match ty with
    | Arrow (ty1,ty2) -> Some (f ty1 ty2)
    | _ -> None

let destruct_arr : t -> (t * t) option =
  arr_apply ~f:(fun ty1 ty2 -> (ty1,ty2))

let destruct_arr_exn (t : t) : t * t =
  Option.value_exn (destruct_arr t)

let id_apply (type a) ~(f:Id.t -> a) (ty:t) : a option =
  match ty with
    | Named v -> Some (f v)
    | _ -> None

let destruct_id : t -> Id.t option =
  id_apply ~f:ident

let destruct_id_exn (x:t) : Id.t =
  Option.value_exn (destruct_id x)

let mk_variant (vs:(Id.t * t) list) : t =
  Variant vs

let variant_apply (type a) ~(f:(Id.t * t) list -> a) (ty:t) : a option =
  match ty with
    | Variant its -> Some (f its)
    | _ -> None

let destruct_variant : t -> (Id.t * t) list option =
  variant_apply ~f:ident

let destruct_variant_exn (t:t) : (Id.t * t) list =
  Option.value_exn (destruct_variant t)

let mk_tuple (ts:t list) : t =
  Tuple ts

let tuple_apply (type a) ~(f:t list -> a) (ty:t) : a option =
  match ty with
    | Tuple ts -> Some (f ts)
    | _ -> None

let destruct_tuple : t -> (t list) option =
  tuple_apply ~f:ident

let destruct_tuple_exn (t:t) : t list =
  Option.value_exn (destruct_tuple t)

let mu_apply (type a) ~(f:Id.t -> t -> a) (ty:t) : a option =
  match ty with
    | Mu (i,t)-> Some (f i t)
    | _ -> None

let destruct_mu : t -> (Id.t * t) option =
  mu_apply ~f:(fun i t -> (i,t))

let destruct_mu_exn (t:t) : Id.t * t =
  Option.value_exn (destruct_mu t)

let _unit : t = mk_tuple []

let _t = mk_named "t"

let _bool = mk_named "bool"

let size : t -> int =
  fold ~name_f:(fun _ -> 1)
       ~arr_f:(fun x y -> x+y+1)
       ~tuple_f:(fun ss -> List.fold_left ~f:(+) ~init:1 ss)
       ~mu_f:(fun _ s -> s+1)
       ~variant_f:(List.fold_left ~init:1 ~f:(fun acc (_,i) -> i+acc))
