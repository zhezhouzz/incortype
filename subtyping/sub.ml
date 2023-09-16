open Language
open Zzdatatype.Datatype
open Sugar
open Rty

let debug_counter = ref 0

(* the ghost variables in rty2 are universal, *)
(* the ghost variables in rty1 are existential, *)
(* Consider
   |- [v:int | v > 3] <: [v:int | v > 5] <->
   forall v. forall v2. v2 > 5 -> exists v1. v1 > 3 /\ (v = v1 ==> v = v2) *)

let handle_ghost ctx (rty1, rty2) =
  let g1, rty1 = destruct_ghost_arr_rty rty1 in
  let g2, rty2 = destruct_ghost_arr_rty rty2 in
  let ctx = ctx @@ List.map (fun (x, cty) -> (x, cty_to_overrty cty)) g1 in
  let ctx = ctx @@ List.map (fun (x, cty) -> (x, cty_to_underrty cty)) g2 in
  (ctx, (rty1, rty2))

let rec sub_rty_bool_normal ctx (rty1, rty2) =
  match (rty1, rty2) with
  | BaseRty { cty = cty1 }, BaseRty { cty = cty2 } ->
      Subcty.sub_cty_bool ctx (cty1, cty2)
  | ( ArrRty { arr_kind = NormalArr; rarg = rarg1; retrty = retrty1 },
      ArrRty { arr_kind = NormalArr; rarg = rarg2; retrty = retrty2 } ) ->
      let arg_bool = sub_rty_bool_normal ctx (rarg2.rty, rarg1.rty) in
      let ctx' =
        match (rarg1.rx, rarg2.rx) with
        | None, None -> ctx
        | Some rx, None | None, Some rx ->
            RTypectx.new_to_right ctx (rx, rarg2.rty)
        | Some rx, Some rx' ->
            let () =
              _assert __FILE__ __LINE__ "subtyping should be unified"
                (String.equal rx rx')
            in
            RTypectx.new_to_right ctx (rx, rarg2.rty)
      in
      arg_bool && sub_rty_bool_normal ctx' (retrty1, retrty2)
  | _, _ -> _failatwith __FILE__ __LINE__ "die"

let sub_rty_bool ctx (rty1, rty2) =
  let ctx, (rty1, rty2) = handle_ghost ctx (rty1, rty2) in
  sub_rty_bool_normal ctx (rty1, rty2)

let is_bot_rty ctx = function
  | BaseRty { cty } -> Subcty.is_bot_cty ctx cty
  | rty -> (
      match to_under_rty_opt rty with
      | None -> false
      | Some cty -> Subcty.is_bot_cty ctx cty)
