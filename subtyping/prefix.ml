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

let prefix_force_epr prefix =
  let fa_list, ex_list = prefix_force_epr_ prefix in
  List.map (fun (x, cty) -> (Fa, x, cty)) fa_list
  @ List.map (fun (x, cty) -> (Ex, x, cty)) ex_list

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

let subtypig_to_prop prefix ({ v = v1; phi = phi1 }, { v = v2; phi = phi2 }) =
  if String.equal v1.x v2.x then
    let prefix = (Fa, v1.x, C.mk_top v1.ty) :: prefix in
    to_prefix prefix @@ P.smart_implies phi1 phi2
  else _failatwith __FILE__ __LINE__ "die"
