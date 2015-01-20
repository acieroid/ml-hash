module type HashingSignature = sig
  type t
  val hash: t -> int
  (** A hash function is perfect if the equality of hashes is equivalent to the
      equality of the values hashed. This implies that if the hash is perfect,
      having hash equality is enough to ensure value equality. *)
  val perfect: bool
  val compare: t -> t -> int
end

module type Hashed = sig
  type elt
  type t
  val wrap: elt -> t
  val hash: t -> int
  val compare: t -> t -> int
end

module MakeHashed : functor(Hashing: HashingSignature) -> Hashed with type elt = Hashing.t =
  functor(Hashing: HashingSignature) -> struct
    type elt = Hashing.t
    type t = elt * int
    let wrap x = (x, Hashing.hash x)
    let hash (_, h) = h
    let compare (x, h) (x', h') =
      (* This function does not satisfy the ordering on values, but just checks equality *)
      let hash_cmp = Pervasives.compare h h' in
      if hash_cmp == 0 && not Hashing.perfect then
        Pervasives.compare x x'
      else
        hash_cmp
  end

module MakeExplicitHashedSet = functor(Hashing: HashingSignature) -> struct
  module Hashed = MakeHashed(Hashing)
  module S = Set.Make(Hashed)
  include S
  let wrap: Hashed.elt -> S.elt = Hashed.wrap
end

module MakeExplicitHashedMap = functor(Hashing: HashingSignature) -> struct
  module Hashed = MakeHashed(Hashing)
  module M = Map.Make(Hashed)
  include M
  let wrap: Hashed.elt -> M.key = Hashed.wrap
end

(* Used like this:
module HashingInt = struct
  type t = int
  let hash x = x
  let perfect = true
  let compare = Pervasives.compare
end

module IntSet = MakeExplicitHashedSet(HashingInt)
module IntMap = MakeExplicitHashedMap(HashingInt)

let () =
  Printf.printf "%b\n" (IntSet.mem (IntSet.wrap 4) (IntSet.add (IntSet.wrap 3) (IntSet.add (IntSet.wrap 4) IntSet.empty)))
*)
