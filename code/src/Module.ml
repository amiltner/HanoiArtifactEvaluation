open Core

module Specification = struct
  type t = Id.t * (Id.t * Type.t) list
  [@@deriving bin_io, eq, hash, ord, sexp, show]
end

module Implementation = struct
  type t = Declaration.t list
  [@@deriving bin_io, eq, hash, ord, sexp, show]
end
