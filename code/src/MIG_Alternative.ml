open Core

module Make
    (V : Verifier.t)
    (S : Synthesizer.t)
    (L : LR.t)
= struct
  module VPIE = VPIE_Alternative.Make(V)(S)(L)

  let push_boundary
      ~(problem : Problem.t)
      ~eval:(eval : Expr.t)
      ~(eval_t : Type.t)
      ~post:(post : Value.t LR.condition)
      ~positives:(positives : Value.t list)
    : Value.t list * Value.t list =
    Log.info
      (lazy ("Checking boundary for:" ^ (DSToMyth.full_to_pretty_myth_string ~problem eval)));
    Consts.full_time
      Consts.verification_times
      Consts.max_verification_time
      Consts.verification_calls
      (fun () -> (L.verifier
                    ~problem
                    eval_t
                    post
                    (LR.Set positives)
                    (Eval.evaluate_with_holes_basic ~tc:problem.tc ~eval_context:problem.eval_context eval)))

  let satisfyTransAll
      ~problem:(problem : Problem.t)
      ~invariant:(invariant : Expr.t)
      ~positives:(positives : Value.t list)
    : ((Expr.t,Value.t list) Core.Either.t) =
    let check_boundary
        (invariant:Expr.t)
      : Value.t list * Value.t list =
      let post =
        LR.Predicate
          (fun v ->
             Value.equal
               Value.mk_true
               (Eval.evaluate_with_holes_basic
                  ~eval_context:problem.eval_context
                  ~tc:problem.tc
                  (Expr.mk_app
                     invariant
                     (Value.to_exp v))))
      in
      List.fold_left
        ~f:(fun acc (eval,eval_t) ->
            begin match acc with
              | ([],[]) ->
                push_boundary
                  ~problem
                  ~eval
                  ~eval_t
                  ~post
                  ~positives
              | _ -> acc
            end)
        ~init:([],[])
        problem.mod_vals
    in
    let rec helper
        (invariant : Expr.t)
      : ((Expr.t,Value.t list) Either.t) =
      let post =
        LR.Predicate
          (fun v ->
             Value.equal
               Value.mk_true
               (Eval.evaluate_with_holes_basic
                  ~tc:problem.tc
                  ~eval_context:problem.eval_context
                  (Expr.mk_app
                     invariant
                     (Value.to_exp v))))
      in
      let pre_or_ce =
        VPIE.learnVPreCondAll
          ~problem
          ~pre:invariant
          ~post
          ~positives:positives
          ~checker:check_boundary
      in
      Log.info
        (lazy ("IND >> Strengthening for inductiveness:"
               ^ (Log.indented_sep 4)
               ^ (DSToMyth.full_to_pretty_myth_string ~problem invariant))) ;
      begin match pre_or_ce with
        | First pre_inv ->
          Log.debug (lazy ("IND Delta: " ^ (DSToMyth.full_to_pretty_myth_string ~problem  pre_inv))) ;
          if Expr.equal pre_inv (Expr.mk_constant_true_func (Type._t)) then
            First (Expr.and_predicates pre_inv invariant)
          else
            helper (Expr.and_predicates pre_inv invariant)
        | Second m ->
          Log.info
            (lazy ("Boundary Not Satisfied, counterexample:"
                   ^ (Log.indented_sep 4)
                   ^ (List.to_string ~f:Value.show (snd m))
                   ^ (Log.indented_sep 4)
                   ^ "Comes from"
                   ^ (Log.indented_sep 4)
                   ^ (List.to_string ~f:Value.show (fst m)))) ;
          Second (snd m)
      end
    in
    helper invariant

  let learnInvariant_internal_smallest50
      ~(unprocessed_problem : Problem.t_unprocessed)
    : string =
    let problem = Problem.process unprocessed_problem in
    (* find I => Q *)
    let (ps,_) = problem.post in
    let ps_t =
      List.filter
        ~f:(fun (_,t) -> Type.equal t Type._t)
        ps
    in
    assert (List.length ps_t = 1);
    let int_seq =
      Sequence.unfold
        ~init:0
        ~f:(fun i -> Some (i,i+1))
    in
    let elt_seq =
      Sequence.concat_map
        ~f:(fun i -> Sequence.of_list (Generator.generator problem.tc Type._t i))
        int_seq
    in
    let relevant_elts =
      Sequence.to_list
        (Sequence.take
           elt_seq
           50)
    in
    Log.info (lazy "elements found, building testbed");
    let testbed =
      List.fold_left
        ~f:(fun testbed e ->
            let valid =
              List.is_empty
                (V.true_on_examples
                   ~problem
                   ~examples:[e]
                   ~eval:(Expr.mk_identity_func Type._t)
                   ~eval_t:(Type.mk_arrow Type._t Type._t)
                   ~post:problem.post)
            in
            if valid then
              TestBed.add_pos_test ~testbed e
            else
              TestBed.add_neg_test ~testbed e)
        ~init:(TestBed.create_positive [])
        relevant_elts
    in
    Log.info (lazy ("testbed done, starting synthesis"));
    let (_,es) =
      S.synth
        ~problem
        ~testbed
    in
    Consts.invariant_size := Expr.size (List.hd_exn es);
    DSToMyth.full_to_pretty_myth_string (List.hd_exn es)
      ~problem


  let rec learnInvariant_internal
      ~(problem : Problem.t)
      ~(positives : Value.t list)
      ~(attempt:int)
    : Expr.t =
    let restart_with_new_positives
        (positive : Value.t list)
      : Expr.t =
      begin
        Log.info (lazy ("Restarting inference engine. Attempt was "
                        ^ (string_of_int attempt)
                        ^ ".")) ;
        learnInvariant_internal
          ~problem
          ~positives:(positive@positives)
          ~attempt:(attempt+1)
      end
    in
    (* find I => Q *)
    let initial_invariant =
      VPIE.learnVPreCond
        ~problem
        ~pre:(Expr.mk_constant_true_func problem.module_type)
        ~eval:(Expr.mk_identity_func (Type._t))
        ~eval_t:(Type.mk_arrow (Type._t) (Type._t))
        ~post:problem.post
        ~positives:positives
    in
    (* inductiveness checks and updates to invariants *)
    (* terminates when either all have been processed and found invariant *)
    (* or until it becomes too strong, and a positive counterexample is added *)
    let inv_or_pos =
      satisfyTransAll
        ~problem
        ~invariant:initial_invariant
        ~positives
    in
    match inv_or_pos with
    | First inv -> inv
    | Second ce -> restart_with_new_positives ce

  let learnInvariant ~(unprocessed_problem : Problem.t_unprocessed)
    : string =
    let problem = Problem.process unprocessed_problem in
    let inv =
      learnInvariant_internal
        ~problem
        ~positives:[]
        ~attempt:0
    in
    Consts.invariant_size := Expr.size inv;
    DSToMyth.full_to_pretty_myth_string inv
      ~problem

  let learnInvariantLinearArbitrary
      ~(unprocessed_problem : Problem.t_unprocessed)
    : string =
    let problem = Problem.process unprocessed_problem in
    let inv =
      VPIE.learnInvariantLinearArbitrary
        ~problem
        ~testbed:(TestBed.create_positive [])
        ~invariant:(Expr.mk_constant_true_func Type._t)
    in
    Consts.invariant_size := Expr.size inv;
    DSToMyth.full_to_pretty_myth_string inv
      ~problem
end
