open Core


module ContractArity =
struct
  type t =
    | P
    | Q
  [@@deriving bin_io, eq, hash, ord, sexp, show]

  let switch_arity (c:t) : t =
    begin match c with
      | P -> Q
      | Q -> P
    end
end

module Contract =
struct
  type t =
    | CoArr of t * t
    | CoMatch of (Id.t * t) list
    | CoTuple of t list
    | CoAccept
    | CoCheck
  [@@deriving bin_io, eq, hash, ord, sexp, show]
end

type t =
  | Var of Id.t
  | App of t * t
  | Func of Param.t * t
  | Ctor of Id.t * t
  | Match of t * Id.t * (Id.t * t) list
  | Fix  of Id.t * Type.t * t
  | Tuple of t list
  | Proj of int * t
  | Obligation of Contract.t * ContractArity.t * t
[@@deriving bin_io, eq, hash, ord, sexp, show]

let mk_var (i:Id.t) : t =
  Var i

let fold (type a)
         ~(var_f:Id.t -> a)
         ~(app_f:a -> a -> a)
         ~(func_f:Param.t -> a -> a)
         ~(ctor_f:Id.t -> a -> a)
         ~(match_f:a -> Id.t -> (Id.t * a) list -> a)
         ~(fix_f:Id.t -> Type.t -> a -> a)
         ~(tuple_f:a list -> a)
         ~(proj_f:int -> a -> a)
         ~(obligation_f:Contract.t -> ContractArity.t -> a -> a)
         (e:t)
         : a =
  let rec fold_internal (e:t) : a =
    match e with
      | Var v -> var_f v
      | App (e1,e2) -> app_f (fold_internal e1) (fold_internal e2)
      | Func (a,e) -> func_f a (fold_internal e)
      | Ctor (v,e) -> ctor_f v (fold_internal e)
      | Match (e,i,branches)
        -> match_f (fold_internal e) i
                   (List.map ~f:(fun (i,e') -> (i,fold_internal e')) branches)
      | Fix (i,t,e)
        -> fix_f i t (fold_internal e)
      | Tuple es
        -> tuple_f (List.map ~f:fold_internal es)
      | Proj (i,e)
        -> proj_f i (fold_internal e)
      | Obligation (c,a,e)
        -> obligation_f c a (fold_internal e)
  in fold_internal e

let mk_app (e1:t) (e2:t) : t =
  App (e1,e2)

let apply_app
    (type a)
    ~(f:t -> t -> a)
    (e:t)
  : a option =
  begin match e with
    | App (e1,e2) -> Some (f e1 e2)
    | _ -> None
  end

let destruct_app
  : t -> (t * t) option =
  apply_app ~f:(fun e1 e2 -> (e1,e2))

let destruct_app_exn
  (e:t)
  : t * t =
  Option.value_exn (destruct_app e)

let mk_func
    (a:Param.t)
    (e:t)
  : t =
  Func (a,e)

let apply_func
    (type a)
    ~(f:Param.t -> t -> a)
    (e:t)
  : a option =
  begin match e with
    | Func (a,e2) -> Some (f a e2)
    | _ -> None
  end

let destruct_func
  : t -> (Param.t * t) option =
  apply_func ~f:(fun a e2 -> (a,e2))

let destruct_func_exn
    (e:t)
  : Param.t * t =
  Option.value_exn (destruct_func e)

let mk_ctor
    (i:Id.t)
    (e:t)
  : t =
  Ctor (i,e)

let apply_ctor
    (type a)
    ~(f:Id.t -> t -> a)
    (e:t)
  : a option =
  begin match e with
    | Ctor (i,e2) -> Some (f i e2)
    | _ -> None
  end

let destruct_ctor
  : t -> (Id.t * t) option =
  apply_ctor ~f:(fun a e2 -> (a,e2))

let destruct_ctor_exn
    (e:t)
  : Id.t * t =
  Option.value_exn (destruct_ctor e)

let mk_tuple
    (es:t list)
  : t =
  Tuple es

let apply_tuple
    (type a)
    ~(f:t list -> a)
    (e:t)
  : a option =
  begin match e with
    | Tuple es -> Some (f es)
    | _ -> None
  end

let destruct_tuple
  : t -> t list option =
  apply_tuple ~f:ident

let destruct_tuple_exn
    (e:t)
  : t list =
  Option.value_exn (destruct_tuple e)

let mk_proj
    (i:int)
    (e:t)
  : t =
  Proj (i,e)

let apply_proj
    (type a)
    ~(f:int -> t -> a)
    (e:t)
  : a option =
  begin match e with
    | Proj (i,e2) -> Some (f i e2)
    | _ -> None
  end

let destruct_proj
  : t -> (int * t) option =
  apply_proj ~f:(fun a e2 -> (a,e2))

let destruct_proj_exn
    (e:t)
  : int * t =
  Option.value_exn (destruct_proj e)

let mk_obligation
    (t:Contract.t)
    (a:ContractArity.t)
    (e:t)
  : t =
  Obligation (t,a,e)

let apply_obligation
    (type a)
    ~(f:Contract.t -> ContractArity.t -> t -> a)
    (e:t)
  : a option =
  begin match e with
    | Obligation (t,a,e2) -> Some (f t a e2)
    | _ -> None
  end

let destruct_obligation
  : t -> (Contract.t * ContractArity.t * t) option =
  apply_obligation ~f:(fun t a e2 -> (t,a,e2))

let destruct_contract_exn
    (e:t)
  : Contract.t * ContractArity.t * t =
  Option.value_exn (destruct_obligation e)

let mk_match
    (e:t)
    (binder:Id.t)
    (branches:(Id.t * t) list)
  : t =
  Match (e,binder,branches)

let apply_match
    (type a)
    ~(f:t -> Id.t -> (Id.t * t) list -> a)
    (e:t)
  : a option =
  begin match e with
    | Match (e,i,branches) -> Some (f e i branches)
    | _ -> None
  end

let destruct_match
  : t -> (t * Id.t * (Id.t * t) list) option =
  apply_match ~f:(fun e i branches -> (e,i,branches))

let destruct_match_exn
    (e:t)
  : t * Id.t * (Id.t * t) list =
  Option.value_exn (destruct_match e)

let mk_fix
    (i:Id.t)
    (t:Type.t)
    (e:t)
  : t =
  Fix (i,t,e)

let apply_fix
    (type a)
    ~(f:Id.t -> Type.t -> t -> a)
    (e:t)
  : a option =
  begin match e with
    | Fix (i,t,e) -> Some (f i t e)
    | _ -> None
  end

let destruct_fix
  : t -> (Id.t * Type.t * t) option =
  apply_fix ~f:(fun i t e -> (i,t,e))

let destruct_fix_exn
    (e:t)
  : Id.t * Type.t * t =
  Option.value_exn (destruct_fix e)

let rec replace
    (i:Id.t)
    (e_with:t)
    (e:t)
  : t =
  let replace_simple = replace i e_with in
  begin match e with
    | Var i' ->
      if String.equal i i' then
        e_with
      else
        e
    | App (e1,e2) ->
      App (replace_simple e1, replace_simple e2)
    | Func ((i',t),e') ->
      if String.equal i i' then
        e
      else
        Func ((i',t),replace_simple e')
    | Ctor (i,e) ->
      Ctor (i, replace_simple e)
    | Match (e,i',branches) ->
      let branches =
        if Id.equal i i' then
          branches
        else
          List.map
            ~f:(fun (i,e) -> (i,replace_simple e))
            branches
      in
      Match (replace_simple e, i', branches)
    | Fix (i',t,e') ->
      if Id.equal i i' then
        e
      else
        Fix (i',t,replace_simple e')
    | Tuple es ->
      Tuple
        (List.map ~f:replace_simple es)
    | Proj (i,e) ->
      Proj (i,replace_simple e)
    | Obligation (t,a,e) ->
      Obligation (t,a,replace_simple e)
  end

let replace_holes
    ~(i_e:(Id.t * t) list)
    (e:t)
  : t =
  List.fold_left
    ~f:(fun acc (i,e) -> replace i e acc)
    ~init:e
    i_e

let mk_unit : t = mk_tuple []

let mk_true_exp
  : t =
  mk_ctor "True" (mk_tuple [])

let mk_false_exp
  : t =
  mk_ctor "False" (mk_tuple [])

let mk_constant_func
    (t:Type.t)
    (e:t)
  : t =
  mk_func ("x",t) e

let mk_constant_true_func
    (t:Type.t)
  : t =
  mk_constant_func t mk_true_exp

let mk_constant_false_func
    (t:Type.t)
  : t =
  mk_constant_func t mk_false_exp

let mk_identity_func
    (t:Type.t)
  : t =
  mk_func ("x",t) (mk_var "x")

let mk_and_func : t = mk_var "and"

let rec contains_var
    (v:Id.t)
    (e:t)
  : bool =
  let contains_var_simple = contains_var v in
  begin match e with
    | Var i -> Id.equal i v
    | App (e1,e2) -> contains_var_simple e1 || contains_var_simple e2
    | Func ((i,_),e) ->
      if Id.equal i v then
        false
      else
        contains_var_simple e
    | Ctor (_,e) -> contains_var_simple e
    | Match (e,i,branches) ->
      contains_var_simple e ||
      (if Id.equal i v then
          false
        else
          List.exists
            ~f:(fun (_,e) -> contains_var_simple e)
            branches)
    | Fix (i,_,e) ->
      if Id.equal i v then
        false
      else
        contains_var_simple e
    | Tuple es -> List.exists ~f:contains_var_simple es
    | Proj (_,e) -> contains_var_simple e
    | Obligation (_,_,e) -> contains_var_simple e
  end

let rec simplify
    (e:t)
  : t =
  begin match e with
    | Var _ -> e
    | App (e1,e2) ->
      mk_app (simplify e1) (simplify e2)
    | Func (a,e) ->
      mk_func a (simplify e)
    | Match (e,v,branches) ->
      mk_match
        (simplify e)
        v
        (List.map ~f:(fun (i,e) -> (i,simplify e)) branches)
    | Fix (i,t,e) ->
      let e = simplify e in
      if not (contains_var i e) then
        e
      else
        mk_fix i t e
    | Ctor (i,e) ->
      mk_ctor i (simplify e)
    | Tuple es -> mk_tuple (List.map ~f:simplify es)
    | Proj (i,e) -> mk_proj i (simplify e)
    | Obligation (t,a,e) -> mk_obligation t a (simplify e)
  end

let and_exps
    (e1:t)
    (e2:t)
  : t =
  mk_app (mk_app mk_and_func e1) e2

let is_func
    ~(func_internals:t)
    (e:t)
  : bool =
  begin match e with
    | Func (_,e) -> equal e func_internals
    | _ -> false
  end

let and_predicates (e1:t) (e2:t) : t =
  let is_true_func = is_func ~func_internals:mk_true_exp in
  let is_false_func = is_func ~func_internals:mk_false_exp in
  if is_true_func e1 then
    e2
  else if is_true_func e2 then
    e1
  else if is_false_func e1 || is_false_func e2 then
    mk_constant_false_func (Type._t)
  else
    let var = "x" in
    let var_exp = mk_var var in
    let apped_e1 = mk_app e1 var_exp in
    let apped_e2 = mk_app e2 var_exp in
    mk_func
      (var,Type._t)
      (and_exps apped_e1 apped_e2)

let mk_let_in (i:Id.t) (t:Type.t) (e1:t) (e2:t) : t =
  mk_app (mk_func (i,t) e2) e1

let size : t -> int =
  fold ~var_f:(fun _ -> 1)
        ~app_f:(fun x y -> x+y+1)
        ~func_f:(fun (_,t) i -> 1 + (Type.size t) + i)
        ~ctor_f:(fun _ s -> s+1)
        ~match_f:(fun s _ bs -> List.fold_left bs ~init:(s+1)
                                              ~f:(fun acc (_,s) -> s+acc))
        ~fix_f:(fun _ t s -> 1 + (Type.size t) + s)
        ~tuple_f:(List.fold_left~f:(+) ~init:1)
        ~proj_f:(fun _ i -> i+2)
        ~obligation_f:(fun _ _ i -> i + 1)
