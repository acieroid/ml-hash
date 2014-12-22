module type HashingSignature = sig
  type t
  val hash: t -> int
end

module MakeHashed : functor(Hashing: HashingSignature) -> sig
  type elt = Hashing.t
  type t
  val wrap: elt -> t
  val hash: t -> int
  val compare: t -> t -> int
end =
  functor(Hashing: HashingSignature) -> struct
    type elt = Hashing.t
    type t = elt * int
    let wrap x = (x, Hashing.hash x)
    let hash (_, h) = h
    let compare (_, h) (_, h') = Pervasives.compare h h'
  end

module MakeHashedSet = functor(Hashing: HashingSignature) -> struct
  module Hashed = MakeHashed(Hashing)
  module S = Set.Make(Hashed)
  include S
  let wrap: Hashed.elt -> S.elt = Hashed.wrap
end

module MakeHashedMap = functor(Hashing: HashingSignature) -> struct
  module Hashed = MakeHashed(Hashing)
  module M = Map.Make(Hashed)
  include M
  let wrap: Hashed.elt -> M.key = Hashed.wrap
end

module HashingInt = struct
  type t = int
  let hash x = x
end

module IntSet = MakeHashedSet(HashingInt)
module IntMap = MakeHashedMap(HashingInt)
