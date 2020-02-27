type 'a condition =
  | Set of 'a list
  | Predicate of ('a -> bool)

module type t = sig
  val verifier :
    problem:Problem.t ->
    Type.t ->
    Value.t condition ->
    Value.t condition ->
    Value.t ->
    Value.t list * Value.t list
end
