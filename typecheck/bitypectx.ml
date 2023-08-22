open Language
open Sugar
open Zzdatatype.Datatype
module OCtx = RTypectx

type t = { octx : OCtx.t; uctx : Rty.rty StrMap.t }

let new_under_to_ctx { octx; uctx } (name, tau) =
  match StrMap.find_opt uctx name with
  | None ->
      let uctx = StrMap.add name tau uctx in
      { octx; uctx }
  | Some _ -> _failatwith __FILE__ __LINE__ "die"

let new_over_to_ctx { octx; uctx } (name, tau) =
  let octx = OCtx.new_to_right octx (name, tau) in
  { octx; uctx }

let find_opt { octx; uctx } name =
  match OCtx.find_opt octx name with
  | Some tau -> Some tau
  | None -> StrMap.find_opt uctx name

let exists { octx; uctx } name =
  match find_opt { octx; uctx } name with Some _ -> true | None -> false

(* let find_avialable ctx name = *)
(*   match find_opt ctx name with *)
(*   | None -> None *)
(*   | Some (Consumed, _) -> _failatwith __FILE__ __LINE__ "die" *)
(*   | Some (Available, tau) -> Some tau *)
open Rty

(* HACK: is this correct? *)
let add_to_ctx { octx; uctx } (name, tau) =
  match tau with
  | BaseRty { ou = Under; _ } -> new_under_to_ctx { octx; uctx } (name, tau)
  | _ -> new_over_to_ctx { octx; uctx } (name, tau)

let new_to_ctx { octx; uctx } (name, tau) =
  match tau with
  | BaseRty { ou = Under; _ } -> new_under_to_ctx { octx; uctx } (name, tau)
  | _ -> new_over_to_ctx { octx; uctx } (name, tau)

let intersect_cty cty1 cty2 =
  let v, phi1 = to_v_prop cty1 in
  let _, phi2 = to_v_prop cty2 in
  ApprCty { v; phi = P.smart_and [ phi1; phi2 ] }

let intersect tau1 cty2 =
  match tau1 with
  | BaseRty { ou = Under; cty = cty1 } ->
      let cty = intersect_cty cty1 cty2 in
      BaseRty { ou = Under; cty }
  | _ -> _failatwith __FILE__ __LINE__ "die"

let consume_from_ctx { octx; uctx } (name, tau) =
  let () =
    if not (exists { octx; uctx } name) then _failatwith __FILE__ __LINE__ "die"
    else ()
  in
  let constraint_in_uctx uctx (name, cty) =
    List.filter_map
      (fun (name', res) ->
        let res =
          if String.equal name name' then
            match res with
            | Consumed, _ -> res
            | Available, tau -> (Available, intersect tau cty)
          else res
        in
        Some (name', res))
      uctx
  in
  match tau with
  | ArrRty _ -> { octx; uctx }
  | BaseRty { ou; cty } -> (
      match OCtx.find_opt octx name with
      | Some _ -> { octx; uctx }
      | None -> (
          let uctx = constraint_in_uctx uctx (name, cty) in
          match ou with
          | Under -> { octx; uctx = consume_via_dependency uctx name }
          | Over -> { octx; uctx }))

let pretty_print { octx; uctx } =
  Pp.printf "@{<yellow>#Over@}: ";
  OCtx.pretty_print octx;
  Pp.printf " @{<yellow>#Under@}: ";
  UCtx.pretty_print uctx

let from_rctx (octx : RTypectx.t) = { octx; uctx = UCtx.empty }
(* List.map (fun (name, tau) -> (name, (Available, tau))) rctx *)
