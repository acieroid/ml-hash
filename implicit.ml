module type HashingSignature = sig
  type t
  val hash: t -> int
  (** A hash function is perfect if the equality of hashes is equivalent to the
      equality of the values hashed. This implies that if the hash is perfect,
      having hash equality is enough to ensure value equality. *)
  val perfect: bool (* TODO: not used? should be used in compare/equal functions *)
  val compare: t -> t -> int
end

module type Hashed = sig
  type elt
  type t
  val wrap: elt -> t
  val unwrap: t -> elt
  val hash: t -> int
  val compare: t -> t -> int
end

module MakeHashed : functor(Hashing: HashingSignature) -> Hashed with type elt = Hashing.t =
  functor(Hashing: HashingSignature) -> struct
    type elt = Hashing.t
    type t = elt * int
    let wrap x = (x, Hashing.hash x)
    let unwrap (x, _) = x
    let hash (_, h) = h
    let compare (x, h) (x, h') =
      Pervasives.compare h h'
  end

module MakeImplicitHashedSet : functor(Hashing: HashingSignature) -> Set.S with type elt = Hashing.t =
  functor(Hashing: HashingSignature) -> struct
    module Hashed = MakeHashed(Hashing)
    module S = Set.Make(Hashed)

    type elt = Hashing.t
    type t = S.t
    let empty = S.empty
    let is_empty = S.is_empty
    let mem x = S.mem (Hashed.wrap x)
    let add x = S.add (Hashed.wrap x)
    let singleton x = S.singleton (Hashed.wrap x)
    let remove x = S.remove (Hashed.wrap x)
    let union = S.union
    let inter = S.inter
    let diff = S.diff
    let compare = S.compare
    let equal = S.equal
    let subset = S.subset
    let iter f = S.iter (fun x -> f (Hashed.unwrap x))
    let fold f = S.fold (fun x -> f (Hashed.unwrap x))
    let for_all f = S.for_all (fun x -> f (Hashed.unwrap x))
    let exists f = S.exists (fun x -> f (Hashed.unwrap x))
    let filter f = S.filter (fun x -> f (Hashed.unwrap x))
    let partition f = S.partition (fun x -> f (Hashed.unwrap x))
    let cardinal = S.cardinal
    let elements s = List.map Hashed.unwrap (S.elements s)
    (* min_elt and max_elt are not implemented, because the set is ordered by
       hash, and the complexity would be O(n) instead of O(log n).
       They can obviously be implemented but by not implementing them we emphase
       this loss of performance. *)
    let min_elt _ = failwith "min_elt not implemented for hashed sets"
    let max_elt _ = failwith "max_elt not implemented for hashed sets"
    let choose s = Hashed.unwrap (S.choose s)
    let split x = S.split (Hashed.wrap x)
    let find x s = Hashed.unwrap (S.find (Hashed.wrap x) s)
    let of_list l = S.of_list (List.map Hashed.wrap l)
  end

module MakeImplicitHashedMap : functor (Hashing: HashingSignature) -> Map.S with type key = Hashing.t =
  functor(Hashing: HashingSignature) -> struct
    module Hashed = MakeHashed(Hashing)
    module M = Map.Make(Hashed)

    type key = Hashing.t
    type 'a t = 'a M.t
    let empty = M.empty
    let is_empty = M.is_empty
    let mem x = M.mem (Hashed.wrap x)
    let add x = M.add (Hashed.wrap x)
    let singleton x = M.singleton (Hashed.wrap x)
    let remove x = M.remove (Hashed.wrap x)
    let merge f = M.merge (fun x -> f (Hashed.unwrap x))
    let compare = M.compare
    let equal = M.equal
    let iter f = M.iter (fun x -> f (Hashed.unwrap x))
    let fold f = M.fold (fun x -> f (Hashed.unwrap x))
    let for_all f = M.for_all (fun x -> f (Hashed.unwrap x))
    let exists f = M.exists (fun x -> f (Hashed.unwrap x))
    let filter f = M.filter (fun x -> f (Hashed.unwrap x))
    let partition f = M.partition (fun x -> f (Hashed.unwrap x))
    let cardinal = M.cardinal
    let bindings m = List.map (function (k, v) -> (Hashed.unwrap k, v)) (M.bindings m)
    (** min_binding and max_binding are not implement for the same reason as
        min_elt and max_elt are not implemented for sets *)
    let min_binding _ = failwith "min_binding not implemented for hashed sets"
    let max_binding _ = failwith "max_binding not implemented for hashed sets"
    let choose m = match M.choose m with (k, v) -> (Hashed.unwrap k, v)
    let split x = M.split (Hashed.wrap x)
    let find x = M.find (Hashed.wrap x)
    let map = M.map
    let mapi f = M.mapi (fun x -> f (Hashed.unwrap x))
  end

(* Use it like this:
module HashingInt = struct
  type t = int
  let hash x = x
  let perfect = true
  let compare = Pervasives.compare
end

module IntSet = MakeImplicitHashedSet(HashingInt)
module IntMap = MakeImplicitHashedMap(HashingInt)

let () =
  Printf.printf "%b\n" (IntSet.mem 4 (IntSet.add 3 (IntSet.add 4 IntSet.empty)))
*)
