open Syntax
module Raw = RtyRaw
open Rty

let rec force rty =
  match rty with
  | Raw.SingleRty tlit ->
      SingleRty { x = Coersion_lit.force tlit.x; ty = tlit.ty }
  | Raw.BaseRty { cty } -> BaseRty { cty = Coersion_cty.force cty }
  | Raw.ArrRty { arr_kind; rarg; retrty } ->
      let Raw.{ rx; rty } = rarg in
      let rarg = rx #:: (force rty) in
      ArrRty { arr_kind; rarg; retrty = force retrty }

let rec besome rty =
  match rty with
  | SingleRty tlit ->
      Raw.SingleRty { x = Coersion_lit.besome tlit.x; ty = tlit.ty }
  | BaseRty { cty } -> Raw.BaseRty { cty = Coersion_cty.besome cty }
  | ArrRty { arr_kind; rarg; retrty } ->
      let { rx; rty } = rarg in
      let rarg = Raw.(rx #:: (besome rty)) in
      Raw.ArrRty { arr_kind; rarg; retrty = besome retrty }
