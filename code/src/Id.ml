open Core

type t =
  string
[@@deriving bin_io, eq, hash, ord, sexp, show]

let mk_prime (x : t) : t = x ^ "'"
