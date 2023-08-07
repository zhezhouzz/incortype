open Syntax
module Raw = RtyRaw
open Rty

let force_arr_kind = function
  | Raw.NormalArr -> NormalArr
  | Raw.GhostArr -> GhostArr

let besome_arr_kind = function
  | NormalArr -> Raw.NormalArr
  | GhostArr -> Raw.GhostArr

let force_ou_kind = function Raw.Over -> Over | Raw.Under -> Under
let besome_ou_kind = function Over -> Raw.Over | Under -> Raw.Under

let rec force rty =
  match rty with
  | Raw.BaseRty { ou; cty } ->
      BaseRty { ou = force_ou_kind ou; cty = Coersion_cty.force cty }
  | Raw.ArrRty { arr_kind; rarg; retrty } ->
      let arr_kind = force_arr_kind arr_kind in
      let Raw.{ rx; rty } = rarg in
      let rarg = rx #:: (force rty) in
      ArrRty { arr_kind; rarg; retrty = force retrty }

let rec besome rty =
  match rty with
  | BaseRty { ou; cty } ->
      Raw.BaseRty { ou = besome_ou_kind ou; cty = Coersion_cty.besome cty }
  | ArrRty { arr_kind; rarg; retrty } ->
      let arr_kind = besome_arr_kind arr_kind in
      let { rx; rty } = rarg in
      let rarg = Raw.(rx #:: (besome rty)) in
      Raw.ArrRty { arr_kind; rarg; retrty = besome retrty }
