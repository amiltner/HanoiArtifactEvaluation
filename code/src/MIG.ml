module Make
    (V : Verifier.t)
    (S : Synthesizer.t)
    (L : LR.t)
  = struct
  module VPIE = VPIE.Make(V)(S)(L)

  let learnInvariant ~(unprocessed_problem : Problem.t_unprocessed)
                     : string =
    let problem = Problem.process unprocessed_problem in
    let inv =
      VPIE.learnVPreCondTrueAll
        ~problem
        ~post:(problem.post)
    in
    Consts.invariant_size := Expr.size inv;
    DSToMyth.full_to_pretty_myth_string inv
      ~problem
end
