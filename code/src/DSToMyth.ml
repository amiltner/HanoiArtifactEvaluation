open Core

module IdSet = Set.Make(Id)
module MythLang = Myth_folds.Lang

module TypeMap = Map.Make(Type)
type type_to_type = MythLang.MType.t TypeMap.t

let merge_tts tt1 tt2 =
  Map.merge_skewed tt1 tt2
                   ~combine:(fun ~key:_ v1 v2
                             -> if MythLang.MType.equal v1 v2 then
                                  v1
                                else
                                  failwith "conflict")

let rec to_myth_type
    (real_vars:IdSet.t)
    (adjoining_var:Id.t option)
    (tt:type_to_type)
    (t:Type.t)
  : (MythLang.id * MythLang.ctor list) list * MythLang.typ * type_to_type =
  let to_myth_type_simple = to_myth_type real_vars adjoining_var tt in
  begin match TypeMap.find tt t with
    | Some mt -> ([],mt,tt)
    | None ->
      begin match t with
        | Named v ->
          if IdSet.mem real_vars v then
            ([],MythLang.TBase v,tt)
          else
            ([],MythLang.TBase v,tt)(*failwith ("non-real var: " ^ v)*)
        | Arrow (t1,t2) ->
          let (ds1,mt1,tt1) = to_myth_type_simple t1 in
          let (ds2,mt2,tt2) = to_myth_type_simple t2 in
          ((ds1@ds2), MythLang.TArr (mt1, mt2), merge_tts tt1 tt2)
        | Tuple ts ->
          if List.length ts = 0 then
            ([],MythLang.TUnit,tt)
          else
            let (ds,mts,tts) = List.unzip3 (List.map ~f:to_myth_type_simple ts) in
            let tt = List.fold_left tts ~init:TypeMap.empty ~f:merge_tts in
            (List.concat ds, MythLang.TTuple mts, tt)
        | Mu (i,t) ->
          (*let fresh = IdSet.fresh_id used_ids i in*)
          assert
            (Option.is_some (Type.destruct_variant t)
              && (Option.equal Id.equal (Some i) adjoining_var));
          let real_vars = IdSet.add real_vars i in
          to_myth_type real_vars adjoining_var tt t
        | Variant branches ->
          let i = Option.value_exn adjoining_var in
          let (unflattened_bs,its,tts) =
            List.unzip3 (
              List.map
                ~f:(fun (i,t) ->
                      let (b,mt,tt) =
                        to_myth_type real_vars adjoining_var tt t
                       in (b,(i,mt),tt))
                branches)
          in
          let tt = List.fold_left tts ~init:tt ~f:merge_tts in
          let bs = List.concat unflattened_bs in
          let tt = TypeMap.set tt ~key:(Variant branches) ~data:(MythLang.TBase i) in
          ((i,its)::bs, MythLang.TBase i,tt)
      end
  end

let to_myth_type_basic
    (tt:type_to_type)
    (t:Type.t)
  : MythLang.typ =
  snd3 (to_myth_type IdSet.empty None tt t)

let rec to_myth_exp
    (tt:type_to_type)
    (e:Expr.t)
  : MythLang.exp =
  let to_myth_exp = to_myth_exp tt in
  MythLang.create_exp (begin match e with
    | Var i -> MythLang.EVar i
    | App (e1,e2) -> MythLang.EApp (to_myth_exp e1, to_myth_exp e2)
    | Func ((i,t),e) ->
      let mt = to_myth_type_basic tt t in
      MythLang.EFun ((i,mt), to_myth_exp e)
    | Ctor (i,e) ->
      ECtor (i,to_myth_exp e)
    | Match (e,i,branches) ->
      let me = to_myth_exp e in
      let mbranches =
        List.map
          ~f:(fun (b,e) -> ((b,Some (MythLang.PVar i)), to_myth_exp e))
          branches
      in
      MythLang.EMatch (me,mbranches)
    | Fix (i,t,e) ->
      let (t1,t2) = Type.destruct_arr_exn t in
      let ((i',t'),e) = Expr.destruct_func_exn e in
      assert (Type.equal t1 t');
      let mt1 = to_myth_type_basic tt t1 in
      let mt2 = to_myth_type_basic tt t2 in
      let me = to_myth_exp e in
      MythLang.EFix (i, (i',mt1), mt2, me)
    | Tuple es ->
      if List.length es = 0 then
        MythLang.EUnit
      else
        MythLang.ETuple (List.map ~f:to_myth_exp es)
    | Proj (i,e) ->
      MythLang.EProj (i+1, to_myth_exp e)
    | Obligation _ -> failwith "shouldnt happen"
    end)

let convert_decl_list_to_myth
    (ec:Context.Exprs.t)
    (ds:Declaration.t list)
  : MythLang.decl list * type_to_type =
  let (tt,ds) =
    List.fold_left
      ~f:(fun (tt,dsrev) d ->
          Declaration.fold
            ~type_f:(fun i t ->
                let (ctors,mt,tt) = to_myth_type IdSet.empty (Some i) tt t in
                let new_ds =
                  List.map
                    ~f:(fun (i,cs) -> MythLang.DData (i,cs))
                    ctors
                in
                let tt = TypeMap.set tt ~key:(Type.mk_named i) ~data:mt in
                (tt,new_ds@dsrev))
            ~expr_f:(fun i e ->
                let new_d =
                  MythLang.DLet
                    (i
                    ,false
                    ,[]
                    ,to_myth_type_basic tt (Context.find_exn ec i)
                    ,to_myth_exp tt e)
                in
                (tt,new_d::dsrev))
            d)
      ~init:(TypeMap.empty,[])
      ds
  in
  (List.rev ds, tt)

let to_myth_exp_with_problem ~(problem:Problem.t) (e:Expr.t) : MythLang.exp =
  let (decls,modi,_,_,_) = problem.unprocessed in
  let (_,tt) = convert_decl_list_to_myth problem.ec (decls@modi) in
  to_myth_exp tt e

let to_pretty_myth_string ~(problem:Problem.t) (e:Expr.t) : string =
  let me = to_myth_exp_with_problem ~problem e
  in Myth_folds.Pp.pp_exp me

let full_to_pretty_myth_string
    ~(problem:Problem.t)
    (inv:Expr.t)
    : string =
let full_ret = match problem.accumulator with
  | None -> Type._bool
  | Some acc -> Type.mk_tuple [(Type._bool) ; acc]
in
let t' = Context.get_foldable_t problem.tc full_ret in
let (a,modi,c,d,e) = problem.unprocessed in
let modi = modi @ [Declaration.TypeDeclaration (Id.mk_prime "t", t')] in
let problem' = Problem.process (a,modi,c,d,e) in
to_pretty_myth_string inv ~problem:problem'

let convert_problem_examples_type_to_myth
    (p:Problem.t)
    (examples:(Expr.t * Expr.t) list)
    (end_type_option:Type.t option)
  : MythLang.decl list
             * (MythLang.exp * MythLang.exp) list
             * MythLang.typ
             * MythLang.typ =
  let (decls,modi,_,_,_) = p.unprocessed in
  let modi =
    if !Consts.prelude_context then
      List.filter
        ~f:(fun d ->
            begin match d with
              | TypeDeclaration _ -> true
              | ExprDeclaration _ -> false
            end)
        modi
    else
      modi
  in
  let (ds,tt) = convert_decl_list_to_myth p.ec (decls@modi) in
  let examples =
    List.map
      ~f:(fun (e1,e2) -> (to_myth_exp tt e1, to_myth_exp tt e2))
      examples
  in
  let (t,t_end) =
    begin match end_type_option with
      | None ->
        (MythLang.TBase "x",MythLang.TBase "x")
      | Some te ->
        (to_myth_type_basic tt (Type.mk_named "t'")
        ,to_myth_type_basic tt te)
    end
  in
  (ds,examples,t,t_end)
