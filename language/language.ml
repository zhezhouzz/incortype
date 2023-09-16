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
  let layout_cty = To_cty.layout
  let layout_rty = To_rty.layout
  let layout_entry = To_structure.layout_entry
  let layout_structure = To_structure.layout
end

module TypedCore = struct
  include Corelang.F (Nt)

  let layout_term e =
    StructureRaw.layout_term @@ Coersion_termlang.besome_typed_term e

  open Sugar

  let value_to_lit v =
    match v with
    | VVar y -> Lit.Lit.AVar y
    | VConst c -> Lit.Lit.AC c
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let tvalue_to_tlit v = (value_to_lit v.x) #: v.ty

  (* let _value_to_lit file line v = *)
  (*   let lit = *)
  (*     match v.x with *)
  (*     | VVar name -> Rty.P.AVar name *)
  (*     | VConst c -> Rty.P.AC c *)
  (*     | VLam _ -> _failatwith file line "?" *)
  (*     | VFix _ -> _failatwith file line "?" *)
  (*     | VTu _ -> _failatwith file line "?" *)
  (*   in *)
  (*   lit #: v.ty *)
end

module Rty = struct
  include Rty

  let layout_lit lit = To_lit.layout_lit (Coersion_lit.besome lit)
  let layout_prop prop = To_qualifier.layout (Coersion_qualifier.besome prop)
  let layout_cty rty = StructureRaw.layout_cty (Coersion_cty.besome rty)
  let layout_rty rty = StructureRaw.layout_rty (Coersion_rty.besome rty)
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

  let mk_rty_primopctx es =
    let mk_rty_primopctx_ = function
      | Rty { name; rty; kind } -> (
          match (To_op.string_to_op name, kind) with
          | Some op, RtyLib -> [ (op, rty) ]
          | _, _ -> [])
      | _ -> []
    in
    List.concat @@ List.map mk_rty_primopctx_ es

  let mk_rty_ctx es =
    let mk_rty_ctx_ = function
      | Rty { name; rty; kind = RtyLib } -> [ (name, rty) ]
      | _ -> []
    in
    let rctx = List.concat @@ List.map mk_rty_ctx_ es in
    let nctx = List.map (fun (x, rty) -> (x, R.erase_rty rty)) rctx in
    (rctx, nctx)
end

module ROpTypectx = struct
  include Rty

  include Typectx.FOp (struct
    include Rty

    type t = rty

    let layout = layout_rty
  end)
end

module RTypectx = struct
  include Rty

  include Typectx.FString (struct
    include Rty

    type t = rty

    let layout = layout_rty
  end)
end
