open Core

let rec explode (binder: Expr.t) : Myth_folds.Lang.pattern list -> (Expr.t * Id.t) list =
  let rec helper i acc =
    function
    | [] -> acc
    | (Myth_folds.Lang.PVar id) :: plist
      -> helper (i + 1) (((Expr.Proj (i, binder)), id) :: acc) plist
    | (Myth_folds.Lang.PTuple _plist) :: plist
      -> helper (i + 1) ((explode (Expr.Proj (i, binder)) _plist) @ acc) plist
    | _ :: plist
      -> helper (i + 1) acc plist
   in helper 0 []

let rec convert_type : Myth_folds.Lang.typ -> Type.t =
  function [@warning "-8"]
  | TBase id          -> Type.Named id
  | TArr (typ1, typ2) -> Type.Arrow ((convert_type typ1), (convert_type typ2))
  | TTuple (typlist)  -> Type.Tuple (List.map ~f:convert_type typlist)
  | TUnit             -> Type._unit

let convert_arg ((id, typ) : Myth_folds.Lang.arg) : Param.t =
  (id, convert_type typ)

let create_fresh_var (counter:int) : Id.t*int =
  ("N_fresh_var_" ^ (string_of_int counter),counter+1)

let  [@warning "-8"] rec convert_expr (counter:int) (e : Myth_folds.Lang.exp) : Expr.t * int =
  begin match e.node with
  | Myth_folds.Lang.EUnit
    -> (Expr.Tuple [],counter)
  | Myth_folds.Lang.EVar id
    -> (Expr.Var id,counter)
  | Myth_folds.Lang.EApp (exp1, exp2)
    ->
    let (e1,counter) = (convert_expr counter exp1) in
    let (e2,counter) = (convert_expr counter exp2) in
    (Expr.App (e1, e2),counter)
  | Myth_folds.Lang.ECtor (id, exp)
    ->
    let (e,counter) = (convert_expr counter exp) in
    (Expr.Ctor (id, e),counter)
  | Myth_folds.Lang.ETuple explist
    ->
    let (es,counter) =
      List.fold_right
        ~f:(fun e (es,counter) ->
            let (e,counter) = convert_expr counter e in
            (e::es,counter))
        ~init:([],counter)
        explist
    in
    (Expr.Tuple es,counter)
  | Myth_folds.Lang.EProj (int, exp)
    ->
    let (e,counter) = (convert_expr counter exp) in
    (Expr.Proj (int-1, e),counter)
  | Myth_folds.Lang.EFix (id, ((_, arg_typ) as arg), typ, body)
    ->
    let (e,counter) = (convert_expr counter body) in
    (Expr.Fix (id, (convert_type (Myth_folds.Lang.TArr (arg_typ, typ))),
               (Expr.Func ((convert_arg arg), e)))
    ,counter)
  | Myth_folds.Lang.EFun (arg, body)
    ->
    let (e,counter) = (convert_expr counter body) in
    (Expr.Func ((convert_arg arg), e),counter)
  | Myth_folds.Lang.ELet (id, _, arglist, typ, exp, body)
    ->
    let (e,counter) = (convert_expr counter exp) in
    let (body,counter) = (convert_expr counter body) in
    let arglist = (List.map ~f:convert_arg arglist)
        in (Expr.App ((Expr.Fix (id,
                                (List.fold
                                  arglist
                                  ~init:(convert_type typ)
                                  ~f:(fun etyp (_, t) -> Type.Arrow (t, etyp))),
                                (List.fold
                                   arglist
                                   ~init:(e)
                                   ~f:(fun eacc arg -> Expr.Func (arg, eacc))))),
                      (body)),counter)
  | Myth_folds.Lang.EMatch (exp, branchlist)
    -> let (fresh_var,counter) = create_fresh_var counter in
    let (e,counter) = convert_expr counter exp in
    let (branches,counter) =
      List.fold_right
        ~f:(fun b (bs,counter) ->
            let (b,counter) = (convert_branch fresh_var counter b) in
            (b::bs,counter))
        ~init:([],counter)
        branchlist
    in
    (Expr.Match (e,
                fresh_var,
                 branches),counter)
  end

and convert_branch (binder : Id.t) (counter:int) : Myth_folds.Lang.branch -> ((Id.t * Expr.t) * int) =
  function [@warning "-8"]
         | ((id, None), exp) ->
    let (e,counter) = convert_expr counter exp in
    ((id, e),counter)
  | ((id, Some (Myth_folds.Lang.PVar _id)), exp)
    -> let (e,counter) = (convert_expr counter exp) in
    ((id, (Expr.mk_let_in _id Type._unit (Expr.Var binder) e)),counter)
  | ((id, Some (Myth_folds.Lang.PTuple _plist)), exp)
    -> let (e,counter) = (convert_expr counter exp) in
    ((id, (List.fold
               (explode (Expr.Var binder) _plist)
               ~init:e
               ~f:(fun eacc (e, _id) -> Expr.mk_let_in _id Type._unit e eacc))),counter)

let convert_expr (e : Myth_folds.Lang.exp) : Expr.t =
  fst (convert_expr 0 e)
