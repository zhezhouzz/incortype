include Syntax

module NTypectx = struct
  include Nt
  include Typectx.FString (Nt)

  let new_to_right ctx { x; ty } = new_to_right ctx (x, ty)

  let new_to_rights ctx l =
    let l = List.map (fun { x; ty } -> (x, ty)) l in
    new_to_rights ctx l
end

module NOpTypectx = struct
  include Nt
  include Typectx.FOp (Nt)

  (* let to_builtin ctx = List.map (fun (x, ty) -> (Op.BuiltinOp x, ty)) ctx *)
  let new_to_right ctx { x; ty } = new_to_right ctx (x, ty)
end

module StructureRaw = struct
  include StructureRaw

  let layout_term = To_expr.layout
  let layout_term_omit_type = To_expr.layout_omit_type
  let layout_cty = To_cty.layout_cty
  let layout_rty = To_rty.layout_rty
  let layout_uty = To_rty.layout_uty
  let layout_entry = To_structure.layout_entry
  let layout_structure = To_structure.layout
end

module Rty = struct
  include Rty

  let layout_lit lit = To_lit.layout_lit (Coersion_lit.besome lit)
  let layout_prop prop = To_qualifier.layout (Coersion_qualifier.besome prop)
  let layout_cty rty = StructureRaw.layout_cty (Coersion_cty.besome rty)
  let layout_rty rty = StructureRaw.layout_rty (Coersion_rty.besome_rty rty)
  let layout_uty rty = StructureRaw.layout_uty (Coersion_rty.besome_uty rty)
end

module Structure = struct
  include Structure
  module R = Rty

  let layout_term x =
    StructureRaw.layout_term @@ Coersion_termlang.besome_typed_term x

  let layout_term_omit_type x =
    StructureRaw.layout_term_omit_type @@ Coersion_termlang.besome_typed_term x

  let layout_entry x =
    StructureRaw.layout_entry @@ Coersion_structure.besome_entry x

  let layout_structure x =
    StructureRaw.layout_structure @@ Coersion_structure.besome_structure x
end

module POpTypectx = struct
  include Rty

  include Typectx.FOp (struct
    include Rty

    type t = uty

    let layout = layout_uty
  end)
end

module PTypectx = struct
  include Rty

  include Typectx.FString (struct
    include Rty

    type t = uty

    let layout = layout_uty
  end)
end

module RTypectx = struct
  include Rty

  include Typectx.FString (struct
    include Rty

    type t = uty

    let layout = layout_uty
  end)
end
