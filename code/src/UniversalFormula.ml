open Core

type t =
  Param.t list * Expr.t
[@@deriving bin_io, eq, hash, ord, sexp, show]

let to_expr_and_type
    ((ps,e):t)
  : Expr.t * Type.t =
  let e =
    List.fold_right
      ~f:(Expr.mk_func)
      ~init:e
      ps
  in
  let t =
    List.fold_right
      ~f:(fun (_,t1) t2 -> Type.mk_arrow t1 t2)
      ~init:Type._bool
      ps
  in
  (e,t)
