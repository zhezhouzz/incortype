open Language
open TypedCore
open Sugar
open Rty

let rty_subst_value (x, v) tau =
  match v with
  | VVar y -> Rty.subst (x, Lit.Lit.AVar y) tau
  | VConst c -> Rty.subst (x, Lit.Lit.AC c) tau
  | _ -> _failatwith __FILE__ __LINE__ "die"

let builtin_typing (v : value) : rty =
  match v with
  | VConst c ->
      let lit = (Lit.Lit.AC c) #: (Const.infer_const_ty c) in
      BaseRty { ou = Under; cty = C.(EqCty lit) }
  | _ -> _failatwith __FILE__ __LINE__ "unimp"

let cur_opctx = ref ROpTypectx.empty
let op_type_syn name = ROpTypectx.find !cur_opctx name.x
let subtyping_check _ _ = true
