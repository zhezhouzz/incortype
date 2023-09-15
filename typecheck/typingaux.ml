open Language
open TypedCore
open Sugar
open Rty

let rty_subst_value (x, v) tau = Rty.subst (x, value_to_lit v) tau

let builtin_typing (v : value) : rty =
  match v with
  | VConst c ->
      let lit = (Lit.Lit.AC c) #: (Const.infer_const_ty c) in
      BaseRty { refinement_kind = Under; cty = C.(EqCty lit) }
  | _ -> _failatwith __FILE__ __LINE__ "unimp"

let cur_opctx = ref ROpTypectx.empty
let op_type_syn name = ROpTypectx.find !cur_opctx name.x

let dt_type_syn name =
  ROpTypectx.find !cur_opctx (Op.BuiltinOp (spf "_%s" name.x))

let subtyping_check _ _ = true
