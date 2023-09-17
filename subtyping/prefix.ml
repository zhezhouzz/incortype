open Language
open Rty
open Sugar

type prefix = (qt * string * cty) list

let rec ctx_to_prefix (ctx : RTypectx.t) =
  match ctx with
  | [] -> []
  | (x, SingleRty tlit) :: ctx ->
      let cty = from_tlit tlit in
      (Fa, x, cty) :: ctx_to_prefix ctx
  | (x, BaseRty { cty }) :: ctx -> (Fa, x, cty) :: ctx_to_prefix ctx
  | (_, ArrRty { arr_kind = NormalArr; _ }) :: ctx -> ctx_to_prefix ctx
  | (x, rty) :: ctx -> (
      match to_under_rty_opt rty with
      | Some cty -> (Ex, x, cty) :: ctx_to_prefix ctx
      | _ -> _failatwith __FILE__ __LINE__ "die")

let flip_prefix prefix =
  List.map (fun (qt, x, cty) -> (flip_qt qt, x, cty)) prefix

let prefix_force_epr_ prefix =
  let rec aux fa_list ex_list = function
    | [] -> (fa_list, ex_list)
    | (Fa, x, cty) :: prefix -> aux (fa_list @ [ (x, cty) ]) ex_list prefix
    | (Ex, x, cty) :: prefix -> aux fa_list (ex_list @ [ (x, cty) ]) prefix
  in
  aux [] [] prefix

let eqr_list_to_prefix fa_list ex_list =
  List.map (fun (x, cty) -> (Fa, x, cty)) fa_list
  @ List.map (fun (x, cty) -> (Ex, x, cty)) ex_list

let prefix_force_epr prefix =
  let fa_list, ex_list = prefix_force_epr_ prefix in
  eqr_list_to_prefix fa_list ex_list

let rec list_subst (z, lit) prefix =
  match prefix with
  | [] -> []
  | (x, cty) :: prefix ->
      let cty = C.subst (x, lit) cty in
      let prefix =
        if String.equal z x then prefix else list_subst (z, lit) prefix
      in
      (x, cty) :: prefix

let list_subst_id (z, id) prefix = list_subst (z, AVar id) prefix

let rec prefix_subst (z, lit) prefix =
  match prefix with
  | [] -> []
  | (qt, x, cty) :: prefix ->
      let cty = C.subst (x, lit) cty in
      let prefix =
        if String.equal z x then prefix else prefix_subst (z, lit) prefix
      in
      (qt, x, cty) :: prefix

let prefix_subst_id (z, id) prefix = prefix_subst (z, AVar id) prefix

let fresh_list (prefix, cty) =
  let rec aux new_prefix (prefix, cty) =
    match prefix with
    | [] -> (new_prefix, cty)
    | (x, xcty) :: prefix ->
        let x' = Rename.unique x in
        let prefix = list_subst_id (x, x') prefix in
        let cty = C.subst_id (x, x') cty in
        aux (new_prefix @ [ (x', xcty) ]) (prefix, cty)
  in
  aux [] (prefix, cty)

let fresh_list_rty (prefix, rty) =
  let rec aux new_prefix (prefix, rty) =
    match prefix with
    | [] -> (new_prefix, rty)
    | (x, xcty) :: prefix ->
        let x' = Rename.unique x in
        let prefix = list_subst_id (x, x') prefix in
        let rty = subst (x, AVar x') rty in
        aux (new_prefix @ [ (x', xcty) ]) (prefix, rty)
  in
  aux [] (prefix, rty)

let fresh_judgement (prefix, cty) =
  let rec aux new_prefix (prefix, cty) =
    match prefix with
    | [] -> (new_prefix, cty)
    | (qt, x, xcty) :: prefix ->
        let x' = Rename.unique x in
        let prefix = prefix_subst_id (x, x') prefix in
        let cty = C.subst_id (x, x') cty in
        aux (new_prefix @ [ (qt, x', xcty) ]) (prefix, cty)
  in
  aux [] (prefix, cty)

let to_prefix prefix body =
  List.fold_right
    (fun (qt, cx, cty) body ->
      let x, xprop = C.cty_typed_to_prop { cx; cty } in
      match (qt, x.ty) with
      | Fa, Nt.Ty_unit -> smart_implies xprop body
      | Ex, Nt.Ty_unit -> smart_and_to xprop body
      | _, _ -> smart_qted qt (x, xprop) body)
    prefix body

(* let prefix_to_subtyping prefix (cty1, cty2) = *)
(*   let fa_list, ex_list = prefix_force_epr_ prefix in *)
(*   let fa_list1, cty1 = fresh_list (ex_list, cty1) in *)
(*   let prefix = eqr_list_to_prefix (fa_list @ fa_list1) ex_list in *)
(*   (prefix, cty1, cty2) *)

let prefix_to_subtyping ctx (cty1, cty2) =
  let prefix = ctx_to_prefix ctx in
  let fa_list, ex_list = prefix_force_epr_ prefix in
  let fa_list1, cty1 = fresh_list (ex_list, cty1) in
  (fa_list @ fa_list1, ex_list, cty1, cty2)

let prefix_to_subtyping_rty ctx (rty1, rty2) =
  let prefix = ctx_to_prefix ctx in
  let fa_list, ex_list = prefix_force_epr_ prefix in
  let fa_list1, rty1 = fresh_list_rty (ex_list, rty1) in
  (fa_list @ fa_list1, ex_list, rty1, rty2)

let subtypig_to_prop prefix ({ v = v1; phi = phi1 }, { v = v2; phi = phi2 }) =
  if String.equal v1.x v2.x then
    let prefix = (Fa, v1.x, C.mk_top v1.ty) :: prefix in
    to_prefix prefix @@ P.smart_implies phi1 phi2
  else _failatwith __FILE__ __LINE__ "die"

let bilist_to_ctx (fa_list, ex_list) =
  List.map (fun (x, cty) -> (x, cty_to_overrty cty)) fa_list
  @ List.map (fun (x, cty) -> (x, cty_to_underrty cty)) ex_list
