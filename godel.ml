(* TODO: use big ints (or better: any comparable hash type), and actually use Gödel hash *)
open Implicit

module type OrderedType = sig
  type t
  val compare: t -> t -> int
  val to_string: t -> string
end

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
  end

module MakeGodelSet : functor(Ord: OrderedType) -> Set.S with type elt = Ord.t =
  functor(Ord: OrderedType) -> struct
    module H = MakeGodelHashing(Ord)
    module S = MakeImplicitHashedSet(H)
    type elt = S.elt
    type t = int * S.t
    let hash_of_set s = S.fold (fun x acc -> acc * (H.hash x)) s 1
    let empty = (1, S.empty) (* 1 is treated as a special value representing only the empty set *)
    let is_empty (_, s) = S.is_empty s
    let mem_h h' (h, s) = h != 1 && h mod h' = 0
    let mem x (h, s) = mem_h (H.hash x) (h, s)
    let add x (h, s) = let h' = H.hash x in
      if mem_h h' (h, s) then (h, s) else (h * h', S.add x s)
    let singleton x = (H.hash x, S.singleton x)
    let remove x (h, s) = let h' = H.hash x in
      if mem_h h' (h, s) then (h / h', S.remove x s) else (h, s)
    let union (h, s) (h', s') = (lcm h h', S.union s s')
    let inter (h, s) (h', s') = (gcd h h', S.inter s s')
    let diff (h, s) (h', s') = (h / (gcd h h'), S.diff s s')
    let compare (h, s) (h', s') = S.compare s s' (* TODO: use subsumption lemmas *)
    let equal (h, _) (h', _) = h == h'
    let subset (h, _) (h', _) = h / h' == 0
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

(*
module MakeGodelMap: functor(Ord: OrderedType) -> Map.S with type key = Ord.t =
  functor(Ord: OrderedType) -> MakeHashedMap(MakeGodelHashing(Ord))

*)
module GodelIntSet = MakeGodelSet(struct type t = int let compare = Pervasives.compare let to_string = string_of_int end)

let () =
  Printf.printf "%b\n" (GodelIntSet.mem 4 (GodelIntSet.add 3 (GodelIntSet.add 4 GodelIntSet.empty)))

