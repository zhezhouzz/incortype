open Language
open Sugar

(* open Zzdatatype.Datatype *)
open Rty

type t = { octx : RTypectx.t; uctx : RTypectx.t }

let new_under_to_ctx { octx; uctx } (name, tau) =
  let uctx = RTypectx.new_to_right uctx (name, tau) in
  { octx; uctx }

let new_over_to_ctx { octx; uctx } (name, tau) =
  let octx = RTypectx.new_to_right octx (name, tau) in
  { octx; uctx }

let find_opt { octx; uctx } name =
  match RTypectx.find_opt octx name with
  | Some tau -> Some tau
  | None -> RTypectx.find_opt uctx name

let exists { octx; uctx } name =
  match find_opt { octx; uctx } name with Some _ -> true | None -> false

(* HACK: is this correct? *)
let add_to_ctx { octx; uctx } (name, tau) =
  match tau with
  | BaseRty { refinement_kind = Under; _ } ->
      new_under_to_ctx { octx; uctx } (name, tau)
  | _ -> new_over_to_ctx { octx; uctx } (name, tau)

let intersect_cty cty1 cty2 =
  let v, phi1 = to_v_prop cty1 in
  let _, phi2 = to_v_prop cty2 in
  ApprCty { v; phi = P.smart_and [ phi1; phi2 ] }

let intersect tau1 cty2 =
  match tau1 with
  | BaseRty { refinement_kind = Under; cty = cty1 } ->
      let cty = intersect_cty cty1 cty2 in
      BaseRty { refinement_kind = Under; cty }
  | _ -> _failatwith __FILE__ __LINE__ "die"

let update_over_typing { octx; uctx } (name, cty) =
  match RTypectx.find_opt uctx name with
  | None -> _failatwith __FILE__ __LINE__ "die"
  | Some tau ->
      let tau = intersect tau cty in
      let uctx = RTypectx.update uctx (name, tau) in
      { octx; uctx }

let update_under_typing { octx; uctx } (name, cty) =
  match RTypectx.find_opt uctx name with
  | None -> _failatwith __FILE__ __LINE__ "die"
  | Some tau ->
      let tau = intersect tau cty in
      let uctx = RTypectx.update uctx (name, tau) in
      { octx; uctx }

open Zzdatatype.Datatype

let exists_function (x, tau_x) tau =
  match tau_x with
  | BaseRty { refinement_kind = Under; cty } ->
      let x, xprop = cty_typed_to_prop { cx = x; cty } in
      let tau =
        match tau with
        | BaseRty { refinement_kind = Under; cty } ->
            BaseRty
              { refinement_kind = Under; cty = exists_xprop (x, xprop) cty }
        | _ -> _failatwith __FILE__ __LINE__ "die"
      in
      tau
  | _ -> tau

let close_ctx_by_name ({ octx; uctx }, tau) name =
  match List.last_destruct_opt uctx with
  | Some (uctx, (name', tau_x)) when String.equal name name' ->
      let tau = exists_function (name, tau_x) tau in
      ({ octx; uctx }, tau)
  | _ -> _failatwith __FILE__ __LINE__ "die"

let close_ctx_by_diff origin ({ octx; uctx }, tau) =
  let rec aux uctx tau =
    match List.last_destruct_opt uctx with
    | None -> (uctx, tau)
    | Some (uctx, (x, tau_x)) ->
        if exists origin x then (uctx, tau)
        else aux uctx (exists_function (x, tau_x) tau)
  in
  let uctx, tau = aux uctx tau in
  ({ octx; uctx }, tau)

let uctx_eq uctx1 uctx2 =
  List.eq
    (fun (name1, tau1) (name2, tau2) ->
      String.equal name1 name2 && Rty.eq_rty tau1 tau2)
    uctx1 uctx2

let merge_uctx uctx uctx' =
  let rec aux uctx' uctx =
    match uctx' with
    | [] -> uctx
    | (name, tau) :: uctx' -> (
        match RTypectx.find_opt uctx name with
        | Some tau' ->
            if not (Rty.eq_rty tau tau') then
              _failatwith __FILE__ __LINE__ "die"
            else aux uctx' uctx
        | None -> aux uctx' (RTypectx.new_to_right uctx (name, tau)))
  in
  aux uctx' uctx

let merge_ctxs ctxs =
  match ctxs with
  | [] -> _failatwith __FILE__ __LINE__ "die"
  | { octx; uctx } :: ctxs ->
      let octxs, uctxs =
        List.split @@ List.map (fun { octx; uctx } -> (octx, uctx)) ctxs
      in
      let () =
        if List.for_all (uctx_eq uctx) uctxs then ()
        else _failatwith __FILE__ __LINE__ "die"
      in
      let octx = List.fold_left merge_uctx octx octxs in
      { octx; uctx }

(* let tlit2 = TypedCore.tvalue_to_tlit v in *)
(* let tau = mk_unit_from_prop Under @@ mk_eq tlit1 tlit2 in *)
(* let x = Rename.unique "_u" in *)
(* add_to_ctx { octx; uctx } (x, tau) *)

(* let new_eqprop_to_ctx { octx; uctx } (tlit1, v) = *)
(*   let tlit2 = TypedCore.tvalue_to_tlit v in *)
(*   let tau = mk_unit_from_prop Under @@ mk_eq tlit1 tlit2 in *)
(*   let x = Rename.unique "_u" in *)
(*   add_to_ctx { octx; uctx } (x, tau) *)

let pretty_print { octx; uctx } =
  Pp.printf "@{<yellow>#Over@}: ";
  RTypectx.pretty_print octx;
  Pp.printf " @{<yellow>#Under@}: ";
  RTypectx.pretty_print uctx

let from_rctx (octx : RTypectx.t) = { octx; uctx = RTypectx.empty }
