open Core

type t =
  | Func of Param.t * Expr.t
  | Ctor of Id.t * t
  | Tuple of t list
  | CoArr of Param.t * Expr.t * Expr.Contract.t * Expr.Contract.t * Expr.ContractArity.t
[@@deriving bin_io, eq, hash, ord, sexp, show]

let mk_func (a:Param.t) (e:Expr.t) : t =
  Func (a,e)

let apply_func (type a) ~(f:Param.t -> Expr.t -> a) (v:t) : a option =
  begin match v with
    | Func (a,e2) -> Some (f a e2)
    | _ -> None
  end

let destruct_func : t -> (Param.t * Expr.t) option =
  apply_func ~f:(fun a e2 -> (a,e2))

let destruct_func_exn (v:t) : Param.t * Expr.t =
  Option.value_exn (destruct_func v)

let mk_ctor (i:Id.t) (v:t) : t =
  Ctor (i,v)

let apply_ctor (type a) ~(f:Id.t -> t -> a) (v:t) : a option =
  match v with
    | Ctor (i,v) -> Some (f i v)
    | _ -> None

let destruct_ctor : t -> (Id.t * t) option =
  apply_ctor ~f:(fun i v -> (i,v))

let destruct_ctor_exn (v:t) : Id.t * t =
  Option.value_exn (destruct_ctor v)

let mk_tuple (vs:t list) : t =
  Tuple vs

let apply_tuple (type a) ~(f:t list -> a) (v:t) : a option =
  begin match v with
    | Tuple vs -> Some (f vs)
    | _ -> None
  end

let destruct_tuple : t -> t list option =
  apply_tuple ~f:ident

let destruct_tuple_exn (v:t) : t list =
  Option.value_exn (destruct_tuple v)

let mk_true : t = mk_ctor "True" (mk_tuple [])

let mk_false : t = mk_ctor "False" (mk_tuple [])

let rec fold ~(func_f:Param.t -> Expr.t -> 'a)
             ~(ctor_f:Id.t -> 'a -> 'a)
             ~(tuple_f:'a list -> 'a)
             ~(coarr_f:Param.t -> Expr.t -> Expr.Contract.t -> Expr.Contract.t -> Expr.ContractArity.t -> 'a)
            (v:t)
            : 'a =
  let fold_simple = fold ~func_f ~ctor_f ~tuple_f ~coarr_f
   in match v with
        | Func (a,e) -> func_f a e
        | Ctor (i,v) -> ctor_f i (fold_simple v)
        | Tuple vs -> tuple_f (List.map ~f:fold_simple vs)
        | CoArr (p,e,c1,c2,a) -> coarr_f p e c1 c2 a

let to_exp : t -> Expr.t =
  fold ~func_f:Expr.mk_func
       ~ctor_f:Expr.mk_ctor
       ~tuple_f:Expr.mk_tuple
       ~coarr_f:(fun p e c1 c2 coa ->
           let f = Expr.mk_func p e in
           Expr.mk_obligation (CoArr(c1,c2)) coa f)

let rec from_exp (e:Expr.t) : t option =
  match e with
    | Func (a,e)
      -> Some (mk_func a e)
    | Ctor (i,e)
      -> Option.map ~f:(mk_ctor i) (from_exp e)
    | Tuple es
      -> Option.map ~f:mk_tuple (Some (List.filter_map es ~f:from_exp))
    | Var _
    | App _
    | Proj _
    | Match _
    | Fix _
    | Obligation _
      -> None

let from_exp_exn (e:Expr.t) : t =
  Option.value_exn (from_exp e)

let rec subvalues (v:t) : t list =
  v :: begin match v with
         | Func _ -> []
         | Ctor (_,v) -> subvalues v
         | Tuple vs -> List.concat_map ~f:subvalues vs
         | CoArr _ -> failwith "shouldnt happen"
       end

let strict_subvalues (e:t) : t list =
  List.tl_exn (subvalues e)

let size : t -> int =
  fold
    ~func_f:(fun (_,t) e -> 1 + (Type.size t) + (Expr.size e))
    ~ctor_f:(fun _ i -> i+1)
    ~tuple_f:(fun is -> List.fold ~f:(+) ~init:1 is)
    ~coarr_f:(fun _ _ -> failwith "shouldnt happen")
