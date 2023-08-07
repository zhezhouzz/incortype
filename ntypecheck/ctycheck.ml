open Language
open RtyRaw

let check opctx ctx = function
  | ApprCty { v; phi } ->
      let ctx' = NTypectx.new_to_rights ctx [ v ] in
      let phi = Qualifiercheck.check opctx ctx' phi in
      ApprCty { v; phi }
  | EqCty lit ->
      let lit =
        Aux.force_typed @@ Litcheck.check opctx ctx lit.Nt.x #: None lit.Nt.ty
      in
      EqCty lit
