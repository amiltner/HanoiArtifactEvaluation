open Core

type t =
  Id.t * Type.t
[@@deriving bin_io, eq, hash, ord, sexp, show]