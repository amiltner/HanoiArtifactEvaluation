module OurLog = Log

open Core

module Log = OurLog

open Utils

module T : Synthesizer.t = struct
  let synth
      ~(problem:Problem.t)
      ~(testbed:TestBed.t)
    : (Type.t option) * (Expr.t list) =
    let pos_examples = List.map ~f:(fun v -> (Value.to_exp v,Expr.mk_true_exp)) testbed.pos_tests in
    let neg_examples = List.map ~f:(fun v -> (Value.to_exp v,Expr.mk_false_exp)) testbed.neg_tests in
    let examples = pos_examples@neg_examples in
    if (List.length examples = 0) then
      (None,[Expr.mk_constant_true_func (Type.mk_named "t")])
    else
      let (decls,examples,t,_) = DSToMythBasic.convert_problem_examples_type_to_myth problem examples in
      let (sigma,gamma) =
        Myth.Typecheck.Typecheck.check_decls
          Myth.Sigma.Sigma.empty
          Myth.Gamma.Gamma.empty
          decls
      in
      let env = Myth.Eval.gen_init_env decls in
      let w = Myth.Eval.gen_init_world env [Myth.Lang.EPFun examples] in
      (None,
       List.map
         ~f:MythToDSBasic.convert_expr
         (Myth.Synth.synthesize
            sigma
            env
            (Myth.Rtree.create_rtree
               sigma
               gamma
               env
               (TArr (t,TBase "bool")) w 0)))
end
