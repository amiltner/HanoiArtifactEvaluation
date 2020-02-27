open Core

module Make (V : Verifier.t) (S : Synthesizer.t) (L : LR.t) = struct
  module RealVPIE = VPIE.Make(V)(S)(L)
  let negs : Value.t list ref = ref []

  type strengthen_triple = bool * Expr.t * TestBed.t

  (*let fr_to_triple
      (prior_triple:)
      (fr:linearArbitraryFixedResponse)
    : bool * Expr.t * TestBed.t =
    begin match fr with
      | Unchanged -> prior_triple
      | NewInv (e,tb) ->
        (true,e,tb)
    end*)

  type linearArbitraryResponse =
    | NewPos of Value.t list
    | Otherwise of strengthen_triple

  let rec learnInvariantLinearArbitrary
      ~(problem:Problem.t)
      ~(testbed:TestBed.t)
      ~(invariant:Expr.t)
    : Expr.t =
    let synth
        ~(testbed:TestBed.t)
      : Expr.t =
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
      let (_,invariants) =
        Consts.full_time
          Consts.synthesis_times
          Consts.max_synthesis_time
          Consts.synthesis_calls
          (fun () ->
             S.synth
               ~problem
               ~testbed)
      in
      List.hd_exn invariants
    in
    let rec makeInductive
        ((changed,invariant,testbed):strengthen_triple)
        (e:Expr.t)
        (t:Type.t)
      : linearArbitraryResponse =
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
      let (pres,posts) =
        Consts.full_time
          Consts.verification_times
          Consts.max_verification_time
          Consts.verification_calls
          (fun () ->
             L.verifier
               ~problem
               t
               invariant_pred
               invariant_pred
               (Eval.evaluate_with_holes_basic ~tc:problem.tc ~eval_context:problem.eval_context e))
      in
      begin match posts with
        | [] -> Otherwise (changed,invariant,testbed)
        | _ ->
          let valid_new_pres =
            List.filter
              ~f:(fun pre -> not (List.mem ~equal:Value.equal (TestBed.positives ~testbed) pre))
              pres
          in
          begin match valid_new_pres with
            | [] -> NewPos posts
            | vs ->
              let testbed =
                TestBed.add_neg_tests
                  ~testbed
                  vs
              in
              let invariant = synth ~testbed in
              makeInductive (true,invariant,testbed) e t
          end
      end
    in
    let rec makeSufficient
        ((changed,invariant,testbed):strengthen_triple)
      : strengthen_triple =
      begin match
          Consts.full_time
            Consts.verification_times
            Consts.max_verification_time
            Consts.verification_calls
            (fun () -> V.implication_counter_example
                ~problem
                ~pre:invariant
                ~eval:(Expr.mk_identity_func (Type._t))
                ~eval_t:(Type.mk_arrow (Type._t) (Type._t))
                ~post:problem.post)
        with
        | [] -> (changed,invariant,testbed)
        | vs ->
          let vs =
            List.filter
              ~f:(fun v -> not (TestBed.contains_test ~testbed v))
              vs
          in
          let testbed = TestBed.add_neg_tests ~testbed vs in
          let invariant = synth ~testbed in
          makeSufficient
            (true,invariant,testbed)
      end
    in
    let trip = makeSufficient (false,invariant,testbed) in
    let response =
      List.fold_left
        ~f:(fun lar (e,t) ->
            begin match lar with
              | NewPos vs -> NewPos vs
              | Otherwise trip ->
                makeInductive trip e t
            end)
        ~init:(Otherwise trip)
        (problem.mod_vals)
    in
    begin match response with
      | NewPos vs ->
        let testbed = TestBed.remove_all_negatives ~testbed in
        let testbed = TestBed.add_pos_tests ~testbed vs in
        learnInvariantLinearArbitrary
          ~problem
          ~testbed
          ~invariant:(Expr.mk_constant_true_func Type._t)
      | Otherwise (changed,invariant,testbed) ->
        if not changed then
          invariant
        else
          learnInvariantLinearArbitrary ~problem ~testbed ~invariant
    end


  let learnVPreCondAll
      ~(problem : Problem.t)
      ~(pre : Expr.t)
      ~(post : Value.t LR.condition)
      ~(positives : Value.t list)
      ~(checker : Expr.t -> (Value.t list) * (Value.t list))
    : (Expr.t,(Value.t list) * (Value.t list)) Either.t =
    let rec helper
        (attempt:int)
        (testbed:TestBed.t)
        (pres:Expr.t list)
      : (Expr.t,Value.t list * Value.t list) Either.t =
      (Log.info (lazy ("VPIE Attempt "
                       ^ (Int.to_string attempt)
                       ^ "."));
       let pres =
         begin match List.filter ~f:(fun e -> RealVPIE.satisfies_testbed ~problem testbed (ref []) e) pres with
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
             let testbed =
               List.fold_left
                 ~f:(fun tb e ->
                     if not (TestBed.contains_test ~testbed:tb e) then
                       TestBed.add_neg_test ~testbed:tb e
                     else
                          tb)
                 ~init:testbed
                 all_inside_examples
             in
             Log.info (lazy "testbed");
             Log.info (lazy (TestBed.show testbed));
             Consts.full_time
               Consts.synthesis_times
               Consts.max_synthesis_time
               Consts.synthesis_calls
               (fun () ->
                  List.map
                    ~f:(fun e -> assert (RealVPIE.satisfies_testbed ~problem testbed (ref []) e); Expr.simplify e)
                    (snd (S.synth ~problem ~testbed:testbed)))
           | pres ->
             pres
         end
       in
       let synthed_pre = List.hd_exn pres in
       Log.info (lazy ("Candidate Precondition: " ^ (DSToMyth.full_to_pretty_myth_string ~problem synthed_pre)));
       let full_pre = Expr.and_predicates pre synthed_pre in
       let boundary_ce =
         checker full_pre
       in
       begin match boundary_ce with
         | ([],[]) ->
           let model_o =
             List.fold_left
               ~f:(fun acc (eval,eval_t) ->
                   begin match acc with
                     | [] ->
                       Log.info (lazy ("verifying: " ^ DSToMyth.full_to_pretty_myth_string ~problem eval));
                       Consts.full_time
                         Consts.verification_times
                         Consts.max_verification_time
                         Consts.verification_calls
                         (fun () -> fst
                             (L.verifier
                                ~problem
                                eval_t
                                post
                                (LR.Predicate
                                   (fun v ->
                                      Value.equal
                                        Value.mk_true
                                        (Eval.evaluate_with_holes_basic
                                           ~tc:problem.tc
                                           ~eval_context:problem.eval_context
                                           (Expr.mk_app
                                              full_pre
                                              (Value.to_exp v)))))
                                (Eval.evaluate_with_holes_basic ~tc:problem.tc ~eval_context:problem.eval_context eval)))
                     (*V.implication_counter_example
                       ~problem
                       ~pre:full_pre
                         ~eval
                         ~eval_t
                         ~post*)
                     | _ -> acc
                   end)
               ~init:[]
               problem.mod_vals
           in
           begin match model_o with
             | [] ->
               Log.info (lazy ("Verified Precondition: " ^ (DSToMyth.full_to_pretty_myth_string ~problem synthed_pre)));
               First synthed_pre
             | model ->
               let new_negs =
                 List.filter
                   ~f:(fun n -> not (TestBed.contains_test ~testbed n))
                   model
               in
               assert (List.length new_negs > 0);
                 Log.info (lazy ("Add negative examples: " ^ (List.to_string ~f:Value.show model)));
                 helper
                   (attempt+1)
                   (TestBed.add_neg_tests
                      ~testbed
                      new_negs)
                   pres
           end
         | ce -> Second ce
       end)
    in
    let testbed = TestBed.create_positive positives in
    helper 0 testbed [Expr.mk_constant_true_func (Type._t)]

  let learnVPreCond
      ~(problem:Problem.t)
      ~(pre:Expr.t)
      ~(eval : Expr.t)
      ~(eval_t : Type.t)
      ~(post : UniversalFormula.t)
      ~(positives : Value.t list)
    : Expr.t =
    let rec helper
        (attempt:int)
        (testbed:TestBed.t)
      : Expr.t =
       let pres =
         begin match List.filter ~f:(fun (e,r) -> RealVPIE.satisfies_testbed ~problem testbed r e) !RealVPIE.possibilities with
           | [] ->
             (Log.info (lazy ("Learning new precondition set.")));
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
             let testbed =
               List.fold_left
                 ~f:(fun tb e ->
                     if not
                         (TestBed.contains_test ~testbed:tb e) then
                       TestBed.add_neg_test ~testbed:tb e
                     else
                       tb
                   )
                 ~init:testbed
                 all_inside_examples
             in
             Log.info (lazy "testbed");
             Log.info (lazy (TestBed.show testbed));
             let pres =
               Consts.full_time
                 Consts.synthesis_times
                 Consts.max_synthesis_time
                 Consts.synthesis_calls
                 (fun () -> (List.map ~f:(fun e -> (Expr.simplify e,ref [])) (snd (S.synth ~problem ~testbed:testbed)))
                 )
             in RealVPIE.possibilities := pres
               ; pres
           | pres ->
             pres
         end
       in
      (Log.info (lazy ("VPIE Attempt "
                       ^ (Int.to_string attempt)
                       ^ "."));
       let synthed_pre = fst (List.hd_exn pres) in
       Log.info (lazy ("Candidate Precondition: " ^ (DSToMyth.full_to_pretty_myth_string ~problem synthed_pre)));
       let full_pre = Expr.and_predicates pre synthed_pre in
       let model_o =
         Consts.full_time
           Consts.verification_times
           Consts.max_verification_time
           Consts.verification_calls
           (fun () -> V.implication_counter_example
               ~problem
               ~pre:full_pre
               ~eval
               ~eval_t
               ~post)
       in
       begin match model_o with
         | [] ->
           Log.info (lazy ("Verified Precondition: " ^ (DSToMyth.full_to_pretty_myth_string ~problem synthed_pre)));
           synthed_pre
         | model ->
             (*negs := new_neg_example::!negs;*)
           Log.info (lazy ("Add negative example: " ^ (List.to_string ~f:Value.show model)));
           let new_negs =
             List.filter
               ~f:(fun v -> not (TestBed.contains_test ~testbed v))
               model
           in
             helper
               (attempt+1)
               (TestBed.add_neg_tests ~testbed new_negs)
       end)
    in
    let testbed = TestBed.create_positive positives in
    let testbed =
      List.fold
        ~f:(fun testbed n -> TestBed.add_neg_test ~testbed n)
        ~init:testbed
        !negs
    in
    helper 0 testbed
end
