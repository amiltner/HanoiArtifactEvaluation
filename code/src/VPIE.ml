open Core

module Make (V : Verifier.t) (S : Synthesizer.t) (L : LR.t) = struct
  let possibilities : (Expr.t * ((Value.t * Value.t) list) ref) list ref = ref [Expr.mk_constant_true_func (Type._t),ref []]

  let satisfies_testbed
      ~(problem:Problem.t)
      (tb:TestBed.t)
      (anses:((Value.t * Value.t) list) ref)
      (e : Expr.t)
    : bool =
    let run_val
        (p:Value.t)
      : Value.t =
      let ans_o =
        List.Assoc.find
          ~equal:Value.equal
          !anses
          p
      in
      begin match ans_o with
        | Some ans -> ans
        | None ->
          let ans =
            Eval.evaluate_with_holes_basic
              ~tc:problem.tc
              ~eval_context:problem.eval_context
              (Expr.mk_app e (Value.to_exp p))
          in
          anses := (p,ans)::(!anses);
          ans
      end
    in
    List.for_all
      ~f:(fun p ->
          let ans = run_val p in
          Value.equal
            ans
            Value.mk_true)
      tb.pos_tests
      &&
      List.for_all
        ~f:(fun p ->
            let ans = run_val p in
            Value.equal
              ans
              Value.mk_false)
        tb.neg_tests

  let check_boundary
      ~(problem : Problem.t)
      ~(invariant : Expr.t)
      ~(positives : Value.t list)
    : Value.t list =
    let check_boundary_singleton
        ~(problem : Problem.t)
        ~eval:(eval : Expr.t)
        ~(eval_t : Type.t)
        ~post:(post : Value.t LR.condition)
        ~positives:(positives : Value.t list)
      : Value.t list * Value.t list =
      Log.info
        (lazy ("Checking boundary for:" ^ (DSToMyth.full_to_pretty_myth_string ~problem eval)));
      let m =
        L.verifier
          ~problem
          eval_t
          post
          (LR.Set positives)
          (Eval.evaluate_with_holes_basic ~tc:problem.tc ~eval_context:problem.eval_context eval)
      in
      begin match m with
        | ([],[]) ->
          Log.info (lazy ("Safe"));
          m
        | _ ->
          Log.info
            (lazy ("Boundary Not Satisfied, counterexample:"
                   ^ (Log.indented_sep 4)
                   ^ (List.to_string ~f:Value.show (snd m))
                   ^ (Log.indented_sep 4)
                   ^ "Comes from"
                   ^ (Log.indented_sep 4)
                   ^ (List.to_string ~f:Value.show (fst m)))) ;
          m
      end
    in
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
    Consts.full_time
      Consts.verification_times
      Consts.max_verification_time
      Consts.verification_calls
      (fun () ->
         snd
           (List.fold_left
              ~f:(fun acc (eval,eval_t) ->
                  begin match acc with
                    | ([],[]) ->
                      check_boundary_singleton
                        ~problem
                        ~eval
                        ~eval_t
                        ~post
                        ~positives
                    | _ -> acc
                  end)
              ~init:([],[])
              problem.mod_vals))

  let valid_answer_lists
      ~(problem:Problem.t)
      ~(answer_lists : (Expr.t * TestBed.t * ((Value.t * Value.t) list) ref * Value.t list) list)
      ~(new_positives : Value.t list)
    : (Expr.t * TestBed.t * ((Value.t * Value.t) list) ref * Value.t list) list =
    let answer_lists =
      List.filter_map
        ~f:(fun (e,tb,anses,ces) ->
            Option.map
              ~f:(fun tb -> (e,tb,anses,ces))
              (TestBed.add_pos_tests_safe ~testbed:tb new_positives))
        answer_lists
    in
    List.filter
      ~f:(fun (e,tb,anses,_) -> satisfies_testbed ~problem tb anses e)
      answer_lists

  let synth_new_inv
      ~(problem:Problem.t)
      ~(testbed:TestBed.t)
    : Expr.t * ((Value.t * Value.t) list) ref =
    possibilities :=
      List.dedup_and_sort
        ~compare:(fun (e1,_) (e2,_) -> Expr.compare e1 e2)
        (List.filter
           ~f:(fun (e1,vr) -> satisfies_testbed ~problem (TestBed.remove_all_negatives ~testbed) vr e1)
           !possibilities);
    begin match List.filter ~f:(fun (e1,vr) -> satisfies_testbed ~problem (TestBed.remove_all_positives ~testbed) vr e1) !possibilities with
      | [] ->
        let subvalues =
          List.concat_map
            ~f:Value.strict_subvalues
            (testbed.pos_tests@testbed.neg_tests)
        in
        let all_inside_examples =
          List.filter
            ~f:(fun e ->
                Typecheck.type_equiv
                  problem.tc
                  (Type._t)
                  (Typecheck.typecheck_exp problem.ec problem.tc problem.vc (Value.to_exp e)))
            subvalues
        in
        (*let ps_t =
          List.filter
            ~f:(fun (_,t) -> Type.equal t Type._t)
            ps
        in
        assert (List.length ps_t = 1);
          let (t_p_i,_) = List.hd_exn ps_t in*)
        let testbed =
          List.fold_left
            ~f:(fun tb e ->
                if TestBed.contains_test ~testbed:tb e then
                  tb
                else
                  TestBed.add_neg_test ~testbed:tb e)
            ~init:testbed
            all_inside_examples
        in
        Log.info (lazy "testbed");
        Log.info (lazy (TestBed.show testbed));
        let results =
          Consts.full_time
            Consts.synthesis_times
            Consts.max_synthesis_time
            Consts.synthesis_calls
            (fun () -> snd (S.synth ~problem ~testbed:testbed))
        in
        let results =
          List.map
            ~f:(fun e ->
                let vr = ref [] in
                assert (satisfies_testbed ~problem testbed vr e); (Expr.simplify e,vr))
            results
        in
        if !Consts.synth_result_persistance then
          possibilities := !possibilities@results;
        List.hd_exn results
      | h::_ ->
        h
    end

  let verify_proves_post
      ~(problem:Problem.t)
      ~(invariant:Expr.t)
      ~(post:UniversalFormula.t)
    : Value.t list =
    Log.info (lazy ("verifying proves postcondition"));
    let vs =
      Consts.full_time
        Consts.verification_times
        Consts.max_verification_time
        Consts.verification_calls
        (fun () ->
           V.implication_counter_example
             ~problem
             ~pre:invariant
             ~eval:(Expr.mk_identity_func (Type._t))
             ~eval_t:(Type.mk_arrow (Type._t) (Type._t))
             ~post)
    in
    begin match vs with
      | [] ->
        Log.info (lazy ("postcondition proven"));
        vs
      | _ ->
        Log.info (lazy ("postcondition unproven, counterexample: "
                       ^ (List.to_string ~f:Value.show vs)));
        vs
    end

  let verify_module
      ~(problem:Problem.t)
      ~(invariant:Expr.t)
    : Value.t list =
    let invariant_pred =
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
    Consts.full_time
      Consts.verification_times
      Consts.max_verification_time
      Consts.verification_calls
      (fun () ->
         List.fold_left
           ~f:(fun acc (eval,eval_t) ->
               begin match acc with
                 | [] ->
                   Log.info (lazy ("verifying: " ^ DSToMyth.full_to_pretty_myth_string ~problem eval));
                   let model =
                     (L.verifier
                        ~problem
                        eval_t
                        invariant_pred
                        invariant_pred
                        (Eval.evaluate_with_holes_basic ~tc:problem.tc ~eval_context:problem.eval_context eval))
                   in
                   begin match model with
                     | ([],[]) -> Log.info (lazy ("Safe")); fst model
                     | _ ->
                       Log.info
                         (lazy ("Not a LR, counterexample:"
                                ^ (Log.indented_sep 4)
                                ^ (List.to_string ~f:Value.show (snd model))
                                ^ (Log.indented_sep 4)
                                ^ "Comes from"
                                ^ (Log.indented_sep 4)
                                ^ (List.to_string ~f:Value.show (fst model)))) ;
                       fst model
                   end
                 (*V.implication_counter_example
                   ~problem
                   ~pre:full_pre
                   ~eval
                   ~eval_t
                   ~post*)
                 | _ -> acc
               end)
           ~init:[]
           problem.mod_vals)


  let learnVPreCondTrueAll
      ~(problem : Problem.t)
      ~(post : UniversalFormula.t)
    : Expr.t =
    let rec learnVPreCondTrueAllInternal
        ~(answer_lists : (Expr.t * TestBed.t * ((Value.t * Value.t) list) ref * Value.t list) list)
      : Expr.t =
      Log.info (lazy ("Answer list length: " ^ (string_of_int (List.length answer_lists))));
      begin match answer_lists with
        | [] -> failwith "something went drastically wrong"
        | (invariant,testbed,anses,ces)::answer_lists ->
          let old_invariant = invariant in
          let old_testbed = testbed in
          Log.info (lazy ("Candidate invariant: " ^ (DSToMyth.full_to_pretty_myth_string ~problem invariant)));
          let overstrong_model =
            check_boundary
              ~problem
              ~invariant
              ~positives:(TestBed.positives ~testbed)
          in
          begin match overstrong_model with
            | [] ->
              let model = ces in
              let model =
                begin match model with
                  | [] ->
                    let model =
                      verify_proves_post
                        ~problem
                        ~invariant
                        ~post
                    in
                    let model =List.filter
                      ~f:(fun n -> not (TestBed.contains_test ~testbed n))
                      model
                    in
                    model
                  | _ ->
                    Log.info (lazy ("Prior counterexample: " ^ (List.to_string ~f:Value.show model)));
                    let model =List.filter
                        ~f:(fun n -> not (TestBed.contains_test ~testbed n))
                        model
                    in
                    if List.is_empty model then
                      failwith "no valid invariant"
                    else
                      model
                end
              in
              let model =
                begin match model with
                  | [] ->
                    if Expr.equal invariant (Expr.mk_constant_true_func Type._t) then
                      []
                    else
                      let model = verify_module ~problem ~invariant in
                      List.filter
                        ~f:(fun n -> not (TestBed.contains_test ~testbed n))
                        model
                  | _ -> model
                end
              in
              begin match model with
                | [] -> invariant
                | _ ->
                  let testbed =
                    TestBed.add_neg_tests
                      ~testbed
                      model
                  in
                  let (new_inv,new_anses) =
                    synth_new_inv
                      ~problem
                      ~testbed
                  in
                  let answer_lists = (new_inv,testbed,new_anses,[])::(old_invariant,old_testbed,anses,model)::answer_lists in
                  learnVPreCondTrueAllInternal
                    ~answer_lists
              end
            | new_positives ->
              let answer_lists =
                if !Consts.counterexample_list_persistance then
                  valid_answer_lists
                    ~problem
                    ~answer_lists
                    ~new_positives
                else
                  let testbed =
                    TestBed.remove_all_negatives
                      ~testbed
                  in
                  let testbed =
                    TestBed.add_pos_tests
                      ~testbed
                      new_positives
                  in
                  [(Expr.mk_constant_true_func Type._t,testbed,ref [],[])]
              in
              learnVPreCondTrueAllInternal
                ~answer_lists
          end
      end
    in
    let true_invariant = Expr.mk_constant_true_func Type._t in
    let false_invariant = Expr.mk_constant_false_func Type._t in
    let testbed = TestBed.create_positive [] in
    let answer_lists = [(false_invariant,testbed,ref [],[]);(true_invariant,testbed,ref [],[])] in
    learnVPreCondTrueAllInternal
      ~answer_lists

end
