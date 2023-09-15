open Syntax
module Raw = RtyRaw.C
open Rty.C

let force Raw.{ v; phi } = { v; phi = Coersion_qualifier.force phi }
let besome { v; phi } = Raw.{ v; phi = Coersion_qualifier.besome phi }
