open Language
open Rty
open Zzdatatype.Datatype
open Sugar

let sub_cty_bool_raw (fa_list, ex_list) (cty1, cty2) =
  let prefix = Prefix.eqr_list_to_prefix fa_list ex_list in
  let query = Prefix.subtypig_to_prop prefix (cty1, cty2) in
  let () =
    Env.show_debug_queries @@ fun _ ->
    Printf.printf "query: %s\n" (layout_prop query)
  in
  let fvs = P.fv query in
  let () =
    _assert __FILE__ __LINE__
      (spf "the cty query has free variables %s" (StrList.to_string fvs))
      (0 == List.length fvs)
  in
  Smtquery.cached_check_bool query

let sub_cty_bool (ctx : RTypectx.t) (cty1, cty2) =
  let fa_list, ex_list, cty1, cty2 =
    Prefix.prefix_to_subtyping ctx (cty1, cty2)
  in
  sub_cty_bool_raw (fa_list, ex_list) (cty1, cty2)

let is_bot_cty pctx cty =
  let bot_cty = C.mk_bot (C.erase cty) in
  sub_cty_bool pctx (cty, bot_cty)

let is_bot_pty pctx pty =
  match pty with
  | BaseRty { cty } -> is_bot_cty pctx cty
  | ArrRty _ | SingleRty _ -> false
