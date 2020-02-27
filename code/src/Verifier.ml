module type t = sig
  val equiv_false :
    problem:Problem.t ->
    cond:Expr.t ->
    bool

  val implication_counter_example :
    problem:Problem.t ->
    pre:Expr.t ->
    eval:Expr.t ->
    eval_t:Type.t ->
    post:UniversalFormula.t ->
    Value.t list

  val true_on_examples :
    problem:Problem.t ->
    examples:Value.t list ->
    eval:Expr.t ->
    eval_t:Type.t ->
    post:UniversalFormula.t ->
    Value.t list
end
