open Syntax
module Raw = RtyRaw.C
open Rty.C

let force = function
  | Raw.ApprCty { v; phi } -> ApprCty { v; phi = Coersion_qualifier.force phi }
  | Raw.EqCty tlit -> EqCty Coersion_lit.force #-> tlit

let besome = function
  | ApprCty { v; phi } -> Raw.ApprCty { v; phi = Coersion_qualifier.besome phi }
  | EqCty tlit -> Raw.EqCty Coersion_lit.besome #-> tlit
