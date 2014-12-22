(* TODO: use big ints (or better: any comparable hash type), and actually use Gödel hash *)
open Implicit

module type OrderedType = sig
  type t
  val compare : t -> t -> int
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
  end

module MakeGodelSet: functor(Ord: OrderedType) -> Set.S with type elt = Ord.t =
  functor(Ord: OrderedType) -> MakeHashedSet(MakeGodelHashing(Ord))
module MakeGodelMap: functor(Ord: OrderedType) -> Map.S with type key = Ord.t =
  functor(Ord: OrderedType) -> MakeHashedMap(MakeGodelHashing(Ord))

module GodelIntSet = MakeGodelSet(struct type t = int let compare = Pervasives.compare end)

let () =
  Printf.printf "%b\n" (GodelIntSet.mem 4 (GodelIntSet.add 3 (GodelIntSet.add 4 GodelIntSet.empty)))

