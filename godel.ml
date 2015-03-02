(* TODO: use big ints (or better: any comparable hash type) if we need more than 50 million elements *)
(* TODO: use Gödel hash as object hash? Might be a bad idea due to the non-definition of the Gödel hash of the empty set/map *)
(* TODO: about benchmark: difference of 2 in the number of words found, probably because of some collision? *)
(* TODO: LazyStream.primes stack overflows after around 40k generated primes *)
(* TODO: About subsumption
  - for sets, it seems that we don't really have to bother with POSets if we implement a simple powerset, the current subsumption used (subseq) is enough
  - for maps, I don't really understand the point. Certainly we can attach a Gödel hash to a map, but it is not used in the actual subsumption checking, which checks subsumption pairwise. Therefore, what's the point of the Gödel hash of the map? only its domain is checked (and its range is iterated over). 
    One solution would be that we can actually just divide those Gödel hash, but this requires the basis decomposition (see written paper) *)

open Implicit

module LazyStream = struct
  type 'a t = Nil | Cons of 'a * ('a t lazy_t)
  let hd = function
    | Nil -> None
    | Cons (h, _) -> Some h
  let tl = function
    | Nil -> Nil
    | Cons (_, t) -> Lazy.force t
  let rec from n = Cons (n, lazy (from (succ n)))
  let rec range a b = if b <= a then Nil else Cons (a, lazy (range (succ a) b))
  let cons hd tl = Cons (hd, tl)
  let rec filter p = function
    | Nil -> Nil
    | Cons (h, t) -> if p h then Cons (h, lazy (filter p (Lazy.force t))) else filter p (Lazy.force t)
  let rec take n = function
    | Nil -> []
    | Cons (h, t) -> if n = 0 then [] else h :: (take (pred n) (Lazy.force t))
  let primes =
    let rec sieve ps =
      let h = match hd ps with
        | Some v -> v
        | None -> failwith "No more primes" in
      cons h (lazy (sieve (filter (fun x -> x mod h != 0) (tl ps)))) in
    sieve (from 2)
end

let rec gcd a b  =
  if b == 0 then a else gcd b (a mod b)
let lcm a b =
  if a == 0 && b == 0 then 0 else (abs (a*b)) / (gcd a b)

module type OrderedType = sig
  type t
  val compare: t -> t -> int
  val to_string: t -> string
end

(** Create a HashingSignature that implements Gödel hashing. That is, the
    module's hash function will cache values in a map, each assigned to a prime
    number, and use those cached primes when called with the same argument *)
module MakeGodelHashing: functor(Ord: OrderedType) -> HashingSignature with type t = Ord.t =
  functor(Ord: OrderedType) -> struct
    module M = Map.Make(Ord)
        type t = Ord.t
        let hash =
          let hashed = ref M.empty in
          let primes = ref LazyStream.primes in
          (fun x ->
             if M.mem x !hashed then
               M.find x !hashed
             else begin
               let prime = match LazyStream.hd !primes with
                 | Some p -> p
                 | None -> failwith "No more primes for Gödel hashing!" in
               primes := LazyStream.tl !primes;
               hashed := M.add x prime !hashed;
               prime
             end)
        let perfect = true
        let compare = Ord.compare
        let to_string = Ord.to_string
  end

(* The HashingSignature should implement a Godel hashing, ie. hashes should be
   prime numbers and the hashing function should be perfect.  This module
   creates a Set module (signature Set.S) that uses Gödel hashing.  The internal
   set contains hashed values (that is, elements of the set are (t, h) where h
   is the Gödel hash). *)
module MakeGodelSet : functor(H: HashingSignature) -> Set.S with type elt = H.t =
  functor(H: HashingSignature) -> struct
    module S = MakeImplicitHashedSet(H)
    type elt = S.elt
    type t = int * S.t
    let hash_of_set s = S.fold (fun x acc -> acc * (H.hash x)) s 1
    let empty = (1, S.empty) (* 1 is treated as a special value representing only the empty set *)
    let is_empty (h, _) = h = 1
    let mem_h h' (h, s) = h != 1 && h mod h' = 0
    let mem x (h, s) = mem_h (H.hash x) (h, s)
    let add x (h, s) = let h' = H.hash x in
      Printf.printf "%d %s\n" h' (H.to_string x);
      if mem_h h' (h, s) then (h, s) else (h * h', S.add x s)
    let singleton x = (H.hash x, S.singleton x)
    let remove x (h, s) = let h' = H.hash x in
      if mem_h h' (h, s) then (h / h', S.remove x s) else (h, s)
    let union (h, s) (h', s') = (lcm h h', S.union s s')
    let inter (h, s) (h', s') = (gcd h h', S.inter s s')
    let diff (h, s) (h', s') = (h / (gcd h h'), S.diff s s')
    let compare (h, s) (h', s') = S.compare s s' (* TODO: use subsumption lemmas *)
    let equal (h, _) (h', _) = h = h'
    let subset (h, _) (h', _) = h mod h' = 0
    let iter f (_, s) = S.iter f s
    let fold f (_, s) = S.fold f s
    let for_all f (_, s) = S.for_all f s
    let exists f (_, s) = S.exists f s
    let filter f (_, s) = let s' = S.filter f s in (hash_of_set s', s')
    let partition f (_, s) = let (s', s'') = S.partition f s in ((hash_of_set s', s'), (hash_of_set s'', s''))
    let cardinal (_, s) = S.cardinal s
    let elements (_, s) = S.elements s
    let min_elt (_, s) = S.min_elt s
    let max_elt (_, s) = S.max_elt s
    let choose (_, s) = S.choose s
    let split x (_, s) = let (s', b, s'') = S.split x s in ((hash_of_set s', s'), b, (hash_of_set s'', s''))
    let find x (h, s) = if mem x (h, s) then x else raise Not_found
    let of_list l = let s = S.of_list l in (hash_of_set s, s)
  end

module type POSetSignature = sig
  type basis
  type t
  val compare: basis -> basis -> int
  val decompose: t -> basis list
  val join: t -> t -> t
  val meet: t -> t -> t
  val to_string: basis -> string
end

module IntPOSet = struct
  type basis = int
  type t = int
  let compare = Pervasives.compare
  let decompose x = [x]
  let join _ _ = failwith "Join not supported by the POSet of integers"
  let meet _ _ = failwith "Meet not supported by the POSet of integers"
  let to_string = string_of_int
end

module AbsBoolPOSet = struct
  type basis = BTrue | BFalse
  type t = Bottom | Bool | True | False
  let compare = Pervasives.compare
  let decompose = function
    | Bottom -> []
    | True -> [BTrue]
    | False -> [BFalse]
    | Bool -> [BTrue; BFalse]
  let join x y = match x, y with
    | True, True -> True
    | False, False -> False
    | True, False | False, True -> Bool
    | Bool, _ | _, Bool -> Bool
    | Bottom, x | x, Bottom -> x
  let meet x y = match x, y with
    | True, True -> True
    | False, False -> False
    | True, False | False, True | Bottom, _ | _, Bottom -> Bottom
    | Bool, x | x, Bool -> x
  let to_string = function
    | BTrue -> "#t"
    | BFalse -> "#f"
end

module type GodelPOSetSignature = sig
  type elt
  type t
  val wrap: elt -> t
  val unwrap: t -> elt
  val join: t -> t -> t
  val meet: t -> t -> t
  val subsumes: t -> t -> bool
  val compare: t -> t -> int
  val to_string: t -> string
end

module MakeGodelPOSet: functor(POSet: POSetSignature) -> GodelPOSetSignature with type elt = POSet.t =
  functor (POSet: POSetSignature) -> struct
    module H = MakeGodelHashing(struct type t = POSet.basis let compare = POSet.compare let to_string = POSet.to_string end)
    type elt = POSet.t
    type t = int * elt
    let hash x = List.fold_left ( * ) 1 (List.map H.hash (POSet.decompose x))
    let wrap x = (hash x, x)
    let unwrap (_, x) = x
    let join (h, x) (h', x') = (lcm h h', POSet.join x x')
    let meet (h, x) (h', x') = (gcd h h', POSet.meet x x')
    let subsumes (h, _) (h', _) = h' mod h = 0
    let compare x y =
      let sub, sub' = subsumes x y, subsumes y x in
      if sub && sub' then 0 else if sub then 1 else -1
    let to_string (h, x) = Printf.sprintf "%d: {%s}" h (String.concat ", " (List.map POSet.to_string (POSet.decompose x)))
  end
(*
module MakeGodelPowerSet: functor(H: HashingSignature) -> GodelPOSetSignature with type elt = Ord.t =
  functor (H: HashingSignature) -> struct
    module S = MakeGodelSet(H)
    type elt = H.t
    type t = int * elt
    let hash x = List.fold_left ( * ) 1 (List.map H.hash (
*)

(* Like Map.S, but without polymorphism. The only restriction it adds is for map
   and mapi, who now need to preserve the type of the stored values *)
module type TypedMap = sig
  type key
  type value
  type t
  val empty : t
  val is_empty : t -> bool
  val mem : key -> t -> bool
  val add : key -> value -> t -> t
  val singleton : key -> value -> t
  val remove : key -> t -> t
  val merge : (key -> value option -> value option -> value option) -> t -> t -> t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val iter : (key -> value -> unit) -> t -> unit
  val fold : (key -> value -> 'a -> 'a) -> t -> 'a -> 'a
  val for_all : (key -> value -> bool) -> t -> bool
  val exists : (key -> value -> bool) -> t -> bool
  val partition : (key -> value -> bool) -> t -> t * t
  val cardinal : t -> int
  val bindings : t -> (key * value) list
  val min_binding : t -> key * value
  val max_binding : t -> key * value
  val choose : t -> key * value
  val split : key -> t -> t * value option * t
  val find : key -> t -> value
  val map : (value -> value) -> t -> t
  val mapi : (key -> value -> value) -> t -> t
end

(** This modules creates a map implementation (with signature Map.S), based storing key-value pairs *)
module MakeGodelMap: functor (Key: OrderedType) -> functor (Value: OrderedType) -> TypedMap with type key = Key.t and type value = Value.t =
  functor (Key: OrderedType) -> functor (Value: OrderedType) -> struct
    module H = MakeGodelHashing(struct
        type t = Key.t * Value.t
        let compare (k1, v1) (k2, v2) =
          let kcomp = Key.compare k1 k2 in
          if kcomp <> 0 then
            Value.compare v1 v2
          else
            kcomp
        let to_string (k, v) = Printf.sprintf "%s: %s" (Key.to_string k) (Value.to_string v)
      end)
    module HK = MakeGodelHashing(Key)
    module M = MakeImplicitHashedMap(HK)
    type key = Key.t
    type value = Value.t
    type t = int * value M.t
    let empty = (1, M.empty)
    let is_empty (h, _) = h = 1
    let find k (_, m) = M.find k m
    let mem k (_, m) = M.mem k m
    let remove k (h, m) =
      if mem k (h, m) then
        let current = find k (h, m) in
        (h / (H.hash (k, current)), M.remove k m)
      else
        (h, m)
    let add k v (h, m) =
      let (h', m') = remove k (h, m) in
      (h' * (H.hash (k, v)), M.add k v m')
    let singleton k v = (H.hash (k, v), M.singleton k v )
    let merge f (_, m) = failwith "TODO"
    let compare (_, m1) (_, m2) = M.compare Value.compare m1 m2 (* TODO: use subsumption lemmas? *)
    let equal (h1, m1) (h2, m2) = h1 == h2
    let iter f (_, m) = M.iter f m
    let fold f (_, m) = M.fold f m
    let for_all f (_, m) = M.for_all f m
    let exists f (_, m) = M.exists f m
    let filter f (_, m) = failwith "TODO"
    let partition f (_, m) = failwith "TODO"
    let cardinal (_, m) = M.cardinal m
    let bindings (_, m) = M.bindings m
    let min_binding (_, m) = M.min_binding m
    let max_binding (_, m) = M.max_binding m
    let choose (_, m) = M.choose m
    let split k (_, m) = failwith "TODO"
    let map f (_, m) = failwith "TODO"
    let mapi f (_, m) = failwith "TODO"
  end

(*
module GodelIntSet = MakeGodelSet(MakeGodelHashing(struct type t = int let compare = Pervasives.compare let to_string = string_of_int end))
module AbsBoolGodelPOSet = MakeGodelPOSet(AbsBoolPOSet)
*)
(*
module GodelInt = MakeGodelHashing(struct type t = int let compare = Pervasives.compare end)
module GodelString = MakeGodelHashing(struct type t = string let compare = Pervasives.compare end)
module IntIntMap = MakeGodelMap(GodelInt)(GodelInt)
module StringIntMap = MakeGodelMap(GodelString)(GodelInt)

let () =
  let m = StringIntMap.singleton "1" 10 in
  let m' = StringIntMap.add "2" 100 m in
  let m'' = StringIntMap.add "3" 1000 m' in
  Printf.printf "%d\n" (StringIntMap.find "3" m'')
*)
