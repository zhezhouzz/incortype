open Language

(* open Zzdatatype.Datatype *)
open Sugar
open Rty

let debug_counter = ref 0

(* the ghost variables in rty2 are universal, *)
(* the ghost variables in rty1 are existential, *)
(* Consider
   |- [v:int | v > 3] <: [v:int | v > 5] <->
   forall v. forall v2. v2 > 5 -> exists v1. v1 > 3 /\ (v = v1 ==> v = v2) *)

let handle_ghost (fa_list, ex_list) (rty1, rty2) =
  let g1, rty1 = destruct_ghost_arr_rty rty1 in
  let g2, rty2 = destruct_ghost_arr_rty rty2 in
  ((fa_list @ g2, ex_list @ g1), (rty1, rty2))

(* let pretty_layout_subtyping ctx (r1, r2) = *)
(*   Env.show_debug_kw __FILE__ (fun _ -> *)
(*       let () = Pp.printf "@{<bold>Subtyping:@}\n" in *)
(*       pretty_print ctx; *)
(*       Pp.printf "⊢\n@{<hi_magenta>%s@} <:\n@{<cyan>%s@}\n" r1 r2) *)

let rec sub_rty_bool_normal (fa_list, ex_list) (rty1, rty2) =
  let () =
    RTypectx.pretty_layout_subtyping
      (Prefix.bilist_to_ctx (fa_list, ex_list))
      (Rty.layout_rty rty1, Rty.layout_rty rty2)
  in
  match (single_to_base rty1, single_to_base rty2) with
  | BaseRty { cty = cty1 }, BaseRty { cty = cty2 } ->
      Subcty.sub_cty_bool_raw (fa_list, ex_list) (cty1, cty2)
  | ( ArrRty { arr_kind = NormalArr; rarg = rarg1; retrty = retrty1 },
      ArrRty { arr_kind = NormalArr; rarg = rarg2; retrty = retrty2 } ) ->
      let arg_bool =
        sub_rty_bool_ghost (fa_list, ex_list) (rarg2.rty, rarg1.rty)
      in
      if not arg_bool then false
      else
        let ctx' =
          match (rarg1.rx, rarg2.rx) with
          | None, None -> []
          | Some rx, None | None, Some rx -> [ (rx, rarg2.rty) ]
          | Some rx, Some rx' ->
              if String.equal rx rx' then [ (rx, rarg2.rty) ]
              else
                _failatwith __FILE__ __LINE__
                  (spf "subtyping should be unified: %s != %s" rx rx')
        in
        let fa_list', ex_list', retrty1, retrty2 =
          Prefix.prefix_to_subtyping_rty ctx' (retrty1, retrty2)
        in
        sub_rty_bool_normal
          (fa_list @ fa_list', ex_list @ ex_list')
          (retrty1, retrty2)
  | _, _ -> _failatwith __FILE__ __LINE__ "die"

and sub_rty_bool_ghost (fa_list, ex_list) (rty1, rty2) =
  let (fa_list, ex_list), (rty1, rty2) =
    handle_ghost (fa_list, ex_list) (rty1, rty2)
  in
  sub_rty_bool_normal (fa_list, ex_list) (rty1, rty2)

let sub_rty_bool ctx (rty1, rty2) =
  let fa_list, ex_list, rty1, rty2 =
    Prefix.prefix_to_subtyping_rty ctx (rty1, rty2)
  in
  sub_rty_bool_ghost (fa_list, ex_list) (rty1, rty2)

let is_bot_rty ctx = function
  | BaseRty { cty } -> Subcty.is_bot_cty ctx cty
  | rty -> (
      match to_under_rty_opt rty with
      | None -> false
      | Some cty -> Subcty.is_bot_cty ctx cty)
