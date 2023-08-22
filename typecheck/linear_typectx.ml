open Language
open Sugar
module OCtx = RTypectx

type linearq = Consumed | Available

let layout_linearq = function
  | Consumed -> "Consumed"
  | Available -> "Available"

module UCtx = Typectx.FString (struct
  include Rty

  type t = linearq * rty

  let layout (linearq, rty) =
    spf "<%s>%s" (layout_linearq linearq) (layout_rty rty)
end)

open Zzdatatype.Datatype

type t = { octx : OCtx.t; uctx : UCtx.t }

let new_avaiable_to_ctx { octx; uctx } (name, tau) =
  let uctx = UCtx.new_to_right uctx (name, (Available, tau)) in
  { octx; uctx }

let new_over_to_ctx { octx; uctx } (name, tau) =
  let octx = OCtx.new_to_right octx (name, tau) in
  { octx; uctx }

let find_opt { octx; uctx } name =
  match OCtx.find_opt octx name with
  | Some tau -> Some tau
  | None -> (
      match UCtx.find_opt uctx name with
      | None -> None
      | Some (Consumed, _) ->
          _failatwith __FILE__ __LINE__ "linear type check error"
      | Some (Available, tau) -> Some tau)

let exists { octx; uctx } name =
  match find_opt { octx; uctx } name with Some _ -> true | None -> false

(* let find_avialable ctx name = *)
(*   match find_opt ctx name with *)
(*   | None -> None *)
(*   | Some (Consumed, _) -> _failatwith __FILE__ __LINE__ "die" *)
(*   | Some (Available, tau) -> Some tau *)
open Rty

(* HACK: is this correct? *)
let new_to_ctx { octx; uctx } (name, tau) =
  match tau with
  | BaseRty { ou = Under; _ } -> new_avaiable_to_ctx { octx; uctx } (name, tau)
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

let consume_via_dependency uctx name =
  let tab = Hashtbl.create 100 in
  let () = Hashtbl.add tab name () in
  let rec aux uctx res =
    match uctx with
    | [] -> res
    | (name, tt) :: uctx when not (Hashtbl.mem tab name) ->
        aux uctx ((name, tt) :: res)
    | (_, (Consumed, _)) :: _ -> _failatwith __FILE__ __LINE__ "die"
    | (name, (Available, tau')) :: uctx ->
        (* let () = *)
        (*   Printf.printf "FV of %s: %s\n" name *)
        (*   @@ StrList.to_string @@ Rty.fv tau' *)
        (* in *)
        let () =
          List.iter (fun name -> Hashtbl.add tab name ()) @@ Rty.fv tau'
        in
        aux uctx ((name, (Consumed, tau')) :: res)
  in
  let uctx = aux (List.rev uctx) [] in
  uctx

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
