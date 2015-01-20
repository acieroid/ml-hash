(** Benchmark map implementation by counting words in a file *)
(* Results on http://norvig.com/big.txt, capped to 50k-1 lines (best execution time over ~5 executions)
     OCaml:
        [Set-Insert] I found 33870 different words in 0.522464 seconds
        [Set-Lookup] I looked up 33870 different words in 0.528084 seconds
        [Map-Insert] I found 33870 different words in 1.007120 seconds
        [Map-Lookup] I looked up 33870 different words in 1.062069 seconds
     ImplicitHashedMap:
        [Set-Insert] I found 33870 different words in 0.580680 seconds
        [Set-Lookup] I looked up 33870 different words in 0.596702 seconds
        [Map-Insert] I found 33870 different words in 1.124777 seconds
        [Map-Lookup] I looked up 33870 different words in 1.177593 seconds
     GodelMap:
        [Primes] I generated 35000 primes in 189.502837 seconds
        [Set-Insert] I found 33868 different words in 1.510693 seconds
        [Set-Lookup] I looked up 33870 different words in 1.427555 seconds
        [Map-Insert] I found 33870 different words in 5.230056 seconds
        [Map-Lookup] I looked up 33870 different words in 5.725221 seconds
*)

let words s = BatString.nsplit s " "

module String = struct type t = string let hash = Hashtbl.hash let perfect = false let compare = Pervasives.compare end
module Int = struct type t = int let hash x =  x let perfect = true let compare = Pervasives.compare end

module S = Set.Make(String)
module M = Map.Make(String)

(*
module S = Implicit.MakeImplicitHashedSet(String)
module M = Implicit.MakeImplicitHashedMap(String)
*)
(*
module S = Godel.MakeGodelSet(Godel.MakeGodelHashing(String))
module M = Godel.MakeGodelMap(Godel.MakeGodelHashing(String))(Godel.MakeGodelHashing(Int))
*)

let count_map_line line counts =
  List.fold_left (fun c w -> if M.mem w c then
                     let cur = M.find w c in
                     M.add w (succ cur) c
                   else
                     M.add w 1 c)
    counts (words line)

let count_set_line line counts =
  List.fold_left (fun c w -> S.add w c) counts (words line)

let count_file file count_f init =
  let rec aux f n counts =
    Printf.printf "\r%d%!" n;
    let line = try Some (input_line f) with End_of_file -> None in
    match line with
    | Some line -> aux f (succ n) (count_f line counts)
    | None -> counts in
  let f = open_in file in
  let res = aux f 0 init in
  close_in f;
  res

let () =
  (* Generate a few primes to see if it accelerates the computation *)
(*  let start0 = Unix.gettimeofday () in
  let ps = Godel.LazyStream.take 35000 Godel.LazyStream.primes in
  let stop0 = Unix.gettimeofday () in
  Printf.printf "[Primes] I generated %d primes in %f seconds\n%!" (List.length ps) (stop0 -. start0);
*)
  (* Set *)
  let start1 = Unix.gettimeofday () in
  let counts_set = count_file "big.txt" count_set_line S.empty in
  let stop1 = Unix.gettimeofday () in
  Printf.printf "\n[Set-Insert] I found %d different words in %f seconds\n%!" (S.cardinal counts_set) (stop1 -. start1);
  let start2 = Unix.gettimeofday () in
  let counts_set = count_file "big.txt" count_set_line counts_set in
  let stop2 = Unix.gettimeofday () in
  Printf.printf "\n[Set-Lookup] I looked up %d different words in %f seconds\n%!" (S.cardinal counts_set) (stop2 -. start2);

  (* Map *)
  let start3 = Unix.gettimeofday () in
  let counts_map = count_file "big.txt" count_map_line M.empty in
  let stop3 = Unix.gettimeofday () in
  Printf.printf "\n[Map-Insert] I found %d different words in %f seconds\n%!" (M.cardinal counts_map) (stop3 -. start3);
  let start4 = Unix.gettimeofday () in
  let counts_map = count_file "big.txt" count_map_line counts_map in
  let stop4 = Unix.gettimeofday () in
  Printf.printf "\n[Map-Lookup] I looked up %d different words in %f seconds\n%!" (M.cardinal counts_map) (stop4 -. start4);
