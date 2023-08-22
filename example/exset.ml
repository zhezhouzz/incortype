module Set = struct
  type set = int list

  let empty = []

  let rec insert (s : set) (elem : int) =
    match s with
    | [] -> [ elem ]
    | h :: t -> if elem < h then elem :: s else h :: insert t elem

  let rec delete (s : set) (elem : int) =
    match s with
    | [] -> s
    | h :: t -> if elem == h then t else h :: delete t elem

  let rec union (s : set) (s' : set) =
    match s with [] -> s' | h :: t -> union t (insert s' h)

  let rec intersect (s : set) (s' : set) =
    match s with [] -> s' | h :: t -> intersect t (delete s' h)

  (* method predicate *)

  let rec size = function [] -> 0 | _ :: t -> 1 + size t

  let rec mem (s : set) (x : int) =
    match s with [] -> false | h :: t -> if h == x then true else mem t x

  let min (s : set) (x : int) = match s with [] -> false | h :: _ -> h == x

  let rec max (s : set) (x : int) =
    match s with [] -> false | [ last ] -> last == x | _ :: t -> max t x

  (* bound *)

  let universal_elem_bound = 5
  let elems = List.init universal_elem_bound (fun x -> x)
  let bound_forall (phi : int -> bool) = List.for_all phi elems
  let bound_exists (phi : int -> bool) = List.exists phi elems

  (* property *)

  let phi_init (s : set) = size s == 0

  let phi_buggy (s : set) =
    size s > 1 && bound_forall (fun (u : int) -> min s u == max s u)

  (* gen and check *)

  let list_size_bound = 7
  let elem_gened = List.init universal_elem_bound (fun x -> x)

  let rec list_gened_ (n : int) =
    if n == 0 then [ [] ]
    else
      let ls = list_gened_ (n - 1) in
      List.fold_left
        (fun r l -> List.map (fun x -> x :: l) elem_gened @ r)
        [] ls

  let list_gened = Array.init list_size_bound list_gened_
  let check1 (phi : set -> bool) = Array.for_all (fun ls -> List.for_all phi ls)

  let check2 (phi : set -> set -> bool) arr =
    check1 (fun s -> check1 (phi s) arr) arr

  (* hypothesis space *)

  let int_literals =
    [
      (fun _ -> 0);
      (fun _ -> 1);
      (fun s -> size s);
      (fun s -> size s + 1);
      (fun s -> size s - 1);
    ]

  type int_lit =
    | Const of int
    | Var of string
    | Size of string
    | Plus of int_lit * int_lit
    | Minus of int_lit * int_lit

  let rec layout_int_lit = function
    | Const i -> string_of_int i
    | Var x -> x
    | Size s -> Printf.sprintf "size(%s)" s
    | Plus (i, j) ->
        Printf.sprintf "%s+%s" (layout_int_lit i) (layout_int_lit j)
    | Minus (i, j) ->
        Printf.sprintf "%s-%s" (layout_int_lit i) (layout_int_lit j)

  type pred =
    | Lt of int_lit * int_lit
    | Eq of int_lit * int_lit
    | Mem of string * int_lit
    | Min of string * int_lit
    | Max of string * int_lit
    | Neg of pred

  let rec layout_pred = function
    | Lt (i, j) -> Printf.sprintf "%s<%s" (layout_int_lit i) (layout_int_lit j)
    | Eq (i, j) -> Printf.sprintf "%s=%s" (layout_int_lit i) (layout_int_lit j)
    | Mem (s, x) -> Printf.sprintf "mem(%s, %s)" s (layout_int_lit x)
    | Min (s, x) -> Printf.sprintf "min(%s, %s)" s (layout_int_lit x)
    | Max (s, x) -> Printf.sprintf "max(%s, %s)" s (layout_int_lit x)
    | Neg p -> Printf.sprintf "~(%s)" (layout_pred p)

  type prop = T | F | Branch of pred * prop * prop

  let rec simp = function
    | T -> T
    | F -> F
    | Branch (pred, p1, p2) -> (
        let p1 = simp p1 in
        let p2 = simp p2 in
        match (p1, p2) with
        | T, T -> T
        | F, F -> F
        | _, _ -> Branch (pred, p1, p2))

  let rec layout_prop = function
    | T -> "T"
    | F -> "F"
    | Branch (_, F, F) -> "F"
    | Branch (_, T, T) -> "T"
    | Branch (pred, T, F) -> layout_pred pred
    | Branch (pred, F, T) -> Printf.sprintf "~(%s)" @@ layout_pred pred
    | Branch (pred, T, p) ->
        Printf.sprintf "(%s \\/ %s)" (layout_pred pred) (layout_prop p)
    | Branch (pred, F, p) ->
        Printf.sprintf "(~(%s) /\\ %s)" (layout_pred pred) (layout_prop p)
    | Branch (pred, p, T) ->
        Printf.sprintf "(~(%s) \\/ %s)" (layout_pred pred) (layout_prop p)
    | Branch (pred, p, F) ->
        Printf.sprintf "(%s /\\ %s)" (layout_pred pred) (layout_prop p)
    | Branch (pred, p1, p2) ->
        Printf.sprintf "(if %s then %s else %s)" (layout_pred pred)
          (layout_prop p1) (layout_prop p2)

  let rec eval_int_lit (s : set) (u : int) = function
    | Const x -> x
    | Var _ -> u
    | Size _ -> List.length s
    | Plus (lit1, lit2) -> eval_int_lit s u lit1 + eval_int_lit s u lit2
    | Minus (lit1, lit2) -> eval_int_lit s u lit1 - eval_int_lit s u lit2

  let rec eval_pred (s : set) (u : int) = function
    | Lt (lit1, lit2) -> eval_int_lit s u lit1 < eval_int_lit s u lit2
    | Eq (lit1, lit2) -> eval_int_lit s u lit1 == eval_int_lit s u lit2
    | Mem (_, lit) -> mem s (eval_int_lit s u lit)
    | Min (_, lit) -> min s (eval_int_lit s u lit)
    | Max (_, lit) -> max s (eval_int_lit s u lit)
    | Neg pred -> not (eval_pred s u pred)

  let int_lits =
    [
      Const 0;
      Const 1;
      Var "u";
      Size "s";
      Plus (Size "s", Const 1);
      Minus (Size "s", Const 1);
    ]

  let preds_ =
    [
      (* Lt (Const 0, Var "u"); *)
      Lt (Const 1, Var "u");
      Lt (Size "s", Var "u");
      Lt (Plus (Size "s", Const 1), Var "u");
      Lt (Minus (Size "s", Const 1), Var "u");
      Lt (Var "u", Size "s");
      Lt (Var "u", Plus (Size "s", Const 1));
      Lt (Var "u", Minus (Size "s", Const 1));
      Eq (Var "u", Const 0);
      Eq (Var "u", Const 1);
      Eq (Var "u", Size "s");
      Eq (Var "u", Plus (Size "s", Const 1));
      Eq (Var "u", Minus (Size "s", Const 1));
      Mem ("s", Var "u");
      Max ("s", Var "u");
      Min ("s", Var "u");
    ]

  let preds = preds_

  let classify_by_pred pred (ss : (set * int) list) =
    List.partition (fun (s, u) -> eval_pred s u pred) ss

  let measure pred pset nset =
    let pset1, pset2 = classify_by_pred pred pset in
    let nset1, nset2 = classify_by_pred pred nset in
    let getf l = float_of_int @@ (1 + List.length l) in
    let getr (p, n) = Float.max (getf p /. getf n) (getf n /. getf p) in
    getr (pset1, nset1) +. getr (pset2, nset2)

  let find_best preds pset nset =
    let p1, p2 =
      List.partition (fun p -> match p with Mem _ -> true | _ -> false) preds
    in
    match p1 with
    | [ p ] -> (p, p2)
    | [] -> (
        let preds = List.map (fun p -> (measure p pset nset, p)) preds in
        let preds = List.sort (fun (f1, _) (f2, _) -> compare f1 f2) preds in
        match preds with
        | (_, p) :: preds -> (p, List.map snd preds)
        | _ -> failwith "die")
    | _ -> failwith "die"

  let rec dt (ftab : pred list) (pset : (set * int) list)
      (nset : (set * int) list) =
    if List.length nset == 0 then T
    else if List.length pset == 0 then F
    else
      match ftab with
      | [] ->
          let _ = Printf.printf "Overapproximated\n" in
          T
      | _ ->
          let pred, ftab = find_best ftab pset nset in
          let pset1, pset2 = classify_by_pred pred pset in
          let nset1, nset2 = classify_by_pred pred nset in
          if
            (List.length pset1 == 0 && List.length nset2 == 0)
            || (List.length pset2 == 0 && List.length nset2 == 0)
          then dt ftab pset nset
          else Branch (pred, dt ftab pset1 nset1, dt ftab pset2 nset2)

  let dt_sim (phi : set -> bool) =
    let ps, ns = List.partition phi (List.concat @@ Array.to_list list_gened) in
    let pset =
      List.concat @@ List.map (fun s -> List.map (fun x -> (s, x)) elems) ps
    in
    let nset =
      List.concat @@ List.map (fun s -> List.map (fun x -> (s, x)) elems) ns
    in
    let prop = simp @@ dt preds pset nset in
    let () = Printf.printf "Result prop: %s\n" (layout_prop prop) in
    ()

  let rec uniq (s : set) =
    match s with [] -> true | h :: t -> if mem t h then false else uniq t

  let test () = dt_sim uniq
end
