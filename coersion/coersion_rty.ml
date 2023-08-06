open Syntax
module Raw = RtyRaw
open Rty

let force_arr_kind = function
  | Raw.NormalArr -> NormalArr
  | Raw.GhostArr -> GhostArr

let besome_arr_kind = function
  | NormalArr -> Raw.NormalArr
  | GhostArr -> Raw.GhostArr

let rec force_rty rty =
  match rty with
  | Raw.BaseRty cty -> BaseRty (Coersion_cty.force cty)
  | Raw.ArrRty { arr_kind; rarg; retrty } ->
      let arr_kind = force_arr_kind arr_kind in
      let Raw.{ ux; uty } = rarg in
      let rarg = ux #::: (force_uty uty) in
      ArrRty { arr_kind; rarg; retrty = force_rty retrty }

and force_uty ty =
  match ty with
  | Raw.BaseUty cty -> BaseUty (Coersion_cty.force cty)
  | Raw.ArrUty rty -> ArrUty (force_rty rty)

let rec besome_rty rty =
  match rty with
  | BaseRty cty -> Raw.BaseRty (Coersion_cty.besome cty)
  | ArrRty { arr_kind; rarg; retrty } ->
      let arr_kind = besome_arr_kind arr_kind in
      let { ux; uty } = rarg in
      let rarg = Raw.(ux #::: (besome_uty uty)) in
      Raw.ArrRty { arr_kind; rarg; retrty = besome_rty retrty }

and besome_uty ty =
  match ty with
  | BaseUty cty -> Raw.BaseUty (Coersion_cty.besome cty)
  | ArrUty rty -> Raw.ArrUty (besome_rty rty)
