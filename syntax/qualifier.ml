open Langlike

module FF (L : Lit.T) = struct
  include L
  include Connective
  open Sexplib.Std

  type prop =
    | Lit of lit
    | Not of prop
    | Ite of prop * prop * prop
    | Binary of binary * prop * prop
    | Multi of multi * prop list
    | Qted of qt * string Nt.typed * prop
  [@@deriving sexp]

  let subst (y, f) e =
    let rec aux e =
      match e with
      | Lit lit -> Lit (L.subst (y, f) lit)
      | Not e -> Not (aux e)
      | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
      | Binary (binary, e1, e2) -> Binary (binary, aux e1, aux e2)
      | Multi (m, es) -> Multi (m, List.map aux es)
      | Qted (qt, u, body) ->
          if String.equal u.x y then e else Qted (qt, u, aux body)
    in
    aux e

  let subst_id (y, z) e = subst (y, AVar z) e
  let msubst = List.fold_right subst
  let msubst_id = List.fold_right subst_id

  let fv e =
    let rec aux e =
      match e with
      | Lit lit -> L.fv lit
      | Not e -> aux e
      | Ite (e1, e2, e3) -> aux e1 @ aux e2 @ aux e3
      | Binary (_, e1, e2) -> aux e1 @ aux e2
      | Multi (_, es) -> List.concat_map aux es
      | Qted (_, u, body) ->
          List.filter (fun x -> not (String.equal x u.x)) @@ aux body
    in
    aux e

  let to_bool_opt = function Lit x -> to_bool_opt x | _ -> None
  let mk_bool b = Lit (mk_bool b)

  let is_bool b p =
    match to_bool_opt p with Some b' -> Bool.equal b b' | _ -> false

  let mk_eq_lit x lit = Lit (L.mk_eq_lit x lit)
  let mk_and l = Multi (And, l)
  let mk_or l = Multi (Or, l)
  let mk_impl a b = Binary (Implies, a, b)
  let mk_iff a b = Binary (Iff, a, b)
  let mk_forall a b = Qted (Fa, a, b)
  let mk_exists a b = Qted (Ex, a, b)
  let mk_prenex = List.fold_right (fun (qt, u) prop -> Qted (qt, u, prop))
  let multi_exists_ qt l = mk_prenex (List.map (fun x -> (qt, x)) l)
  let multi_exists = multi_exists_ Ex
  let multi_forall = multi_exists_ Fa
end

module F (L : Lit.T) = struct
  include L
  include SexpCompare (FF (L))
  include FF (L)

  let multi_default multi = match multi with And -> true | Or -> false
  let multi_shortcut multi = match multi with And -> false | Or -> true

  let smart_multi multi l =
    let default = multi_default multi in
    let shortcut = multi_shortcut multi in
    if List.exists (is_bool shortcut) l then mk_bool shortcut
    else
      match List.filter (fun p -> not (is_bool default p)) l with
      | [] -> mk_bool default
      | [ x ] -> x
      | l -> Multi (multi, l)

  let smart_and = smart_multi And
  let smart_or = smart_multi Or

  let smart_multi_add multi p prop =
    let default = multi_default multi in
    let shortcut = multi_shortcut multi in
    if is_bool shortcut p then mk_bool shortcut
    else if is_bool default p then prop
    else
      match prop with
      | Multi (multi', props) when multi_eq multi multi' ->
          smart_multi multi (p :: props)
      | _ -> Multi (multi, [ p; prop ])

  let smart_and_to = smart_multi_add And
  let smart_or_to = smart_multi_add Or

  (* let smart_add_to a prop = *)
  (*   match to_bool_opt a with *)
  (*   | Some true -> prop *)
  (*   | Some false -> mk_false *)
  (*   | None -> ( *)
  (*       match prop with *)
  (*       | And props -> smart_and (a :: props) *)
  (*       | _ -> smart_and [ a; prop ]) *)

  let smart_implies a prop =
    match to_bool_opt a with
    | Some true -> prop
    | Some false -> mk_bool true
    | None -> mk_impl a prop

  let smart_iff a b =
    match (to_bool_opt a, to_bool_opt b) with
    | Some b, Some b' when b == b' -> mk_bool true
    | Some b, Some b' when b != b' -> mk_bool false
    | _, _ -> mk_impl a b

  let get_eqprop_by_name prop x =
    match prop with Lit lit -> get_eqlit_by_name lit x | _ -> None

  let smart_qted qt (u, xprop) prop =
    let body =
      match qt with
      | Ex -> smart_and_to xprop prop
      | Fa -> smart_implies xprop prop
    in
    match u.Nt.ty with
    | Nt.Ty_unit -> body
    | _ -> (
        match get_eqprop_by_name xprop u.Nt.x with
        | None -> Qted (qt, u, body)
        | Some z -> subst (u.Nt.x, z) prop)

  let smart_sigma = smart_qted Ex
  let smart_pi = smart_qted Fa
  (* open Sugar *)
end
