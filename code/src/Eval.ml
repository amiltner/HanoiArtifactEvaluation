open Core

exception ContractViolation of (Value.t * (Value.t list) * Expr.ContractArity.t)

let rec evaluate
    ~(tc:Context.Types.t)
    ~(p_check:Value.t -> bool)
    ~(q_check:Value.t -> bool)
    ~(log:Expr.ContractArity.t)
    (e : Expr.t)
  : Value.t * Value.t list =
  match e with
  | Var i -> failwith ("unbound variable " ^ i)
  | App (e1,e2) ->
    let (v1,v1s) = evaluate ~tc ~p_check ~q_check ~log e1 in
    let e1 = Value.to_exp v1 in
    begin match e1 with
      | Expr.Func ((i,_),e1) ->
        let (v2,v2s) = evaluate ~tc ~p_check ~q_check ~log e2 in
        let e2 = Value.to_exp v2 in
        let (v,vs) = evaluate ~tc ~p_check ~q_check ~log (Expr.replace i e2 e1) in
        (v,v1s@v2s@vs)
      | Expr.Obligation (c,ca,e1) ->
        begin match c with
          | Expr.Contract.CoArr (c1,c2) ->
            let e2 = Expr.mk_obligation c1 (Expr.ContractArity.switch_arity ca) e2 in
            let e = Expr.mk_app e1 e2 in
            let e = Expr.mk_obligation c2 ca e in
            evaluate ~tc ~p_check ~q_check ~log e
          | _ ->
            failwith "nonarrow contract applied"
        end
      | _ -> failwith "nonfunc, noncontract applied"
    end
  | Func (a,e) ->
    (Value.mk_func a e,[])
  | Ctor (i,e) ->
    let (v,vs) = evaluate ~p_check ~q_check ~log ~tc e in
    (Value.mk_ctor i v,vs)
  | Match (e,i,branches) as match_expr ->
    let (v,vs) = evaluate ~p_check ~q_check ~log ~tc e in
    let (choice,v) = Value.destruct_ctor_exn v in
    let branch_o = List.Assoc.find ~equal:Id.equal branches choice in
    let branch =
      begin match branch_o with
        | None ->
          failwith
            ("constructor "
             ^ choice
             ^ " not matched: \n "
             ^ (Expr.show match_expr))
        | Some b -> b
      end
    in
    let (v,vs') = evaluate ~tc ~p_check ~q_check ~log (Expr.replace i (Value.to_exp v) branch) in
    (v,vs@vs')
  | Fix (i,_,e') ->
    evaluate ~tc ~p_check ~q_check ~log (Expr.replace i e e')
  | Tuple es ->
    let (vs,vsaccs) =
      List.unzip
        (List.map ~f:(evaluate ~tc ~p_check ~q_check ~log) es)
    in
    (Value.mk_tuple vs,List.concat vsaccs)
  | Proj (i,e) ->
    let (v,vs) = evaluate ~tc ~p_check ~q_check ~log e in
    (List.nth_exn (Value.destruct_tuple_exn v) i,vs)
  | Obligation (c,a,e) ->
    let (v,vs) = evaluate ~tc ~p_check ~q_check ~log e in
    let rec propogate_contract
        (c:Expr.Contract.t)
        (a:Expr.ContractArity.t)
        (v:Value.t)
      : Value.t * Value.t list =
      let propogate_contract_simple c v = propogate_contract c a v in
      begin match c with
        | CoArr (c1,c2) ->
          let (p,e) = Value.destruct_func_exn v in
          (Value.CoArr (p,e,c1,c2,a),[])
        | CoCheck ->
          let new_vs = if log = a then [v] else [] in
          begin match a with
            | P ->
              if p_check v then
                (v,new_vs)
              else
                raise (ContractViolation (v,vs@new_vs,a))
            | Q ->
              if q_check v then
                (v,new_vs)
              else
                raise (ContractViolation (v,vs@new_vs,a))
          end
        | CoTuple cs ->
          let vs = Value.destruct_tuple_exn v in
          let (vs,vaccs) =
            List.unzip
              (List.map2_exn ~f:propogate_contract_simple cs vs)
          in
          (Value.mk_tuple vs,List.concat vaccs)
        | CoAccept -> (v,[])
        | CoMatch branches ->
          let (i,v) = Value.destruct_ctor_exn v in
          let t = List.Assoc.find_exn ~equal:Id.equal branches i in
          let (v,vs) = propogate_contract_simple t v in
          (Value.mk_ctor i v,vs)
      end
    in
    let (v,vs') = propogate_contract c a v in
    (v,vs@vs')

let evaluate_with_holes
    ~(tc:Context.Types.t)
    ~eval_context:(i_e:(Id.t * Expr.t) list)
    ~(p_check:Value.t -> bool)
    ~(q_check:Value.t  -> bool)
    ~(log:Expr.ContractArity.t)
    (e:Expr.t)
  : Value.t * Value.t list =
  let e = Expr.replace_holes ~i_e e in
  evaluate ~tc ~p_check ~q_check ~log e

let evaluate_basic
    ~(tc:Context.Types.t)
    (e:Expr.t)
  : Value.t =
  fst (evaluate ~tc ~p_check:(fun _ -> true) ~q_check:(fun _ -> true) ~log:P e)

let evaluate_with_holes_basic
    ~(tc:Context.Types.t)
    ~eval_context:(i_e:(Id.t * Expr.t) list)
    (e:Expr.t)
  : Value.t =
  let e = Expr.replace_holes ~i_e e in
  evaluate_basic ~tc e
