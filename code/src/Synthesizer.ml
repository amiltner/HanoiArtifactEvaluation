module type t = sig
  val synth :
    problem : Problem.t ->
    testbed : TestBed.t ->
    Type.t option * Expr.t list
end
