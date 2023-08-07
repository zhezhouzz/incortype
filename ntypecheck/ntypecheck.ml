open Language
open Sugar
open StructureRaw

let opt_to_typed_rty opctx ctx rty : Rty.rty =
  Coersion_rty.force (Rtycheck.check opctx ctx rty)

let opt_to_typed_cty opctx ctx cty : Rty.cty =
  Coersion_cty.force (Ctycheck.check opctx ctx cty)

open Ttypecheck

let opt_to_typed_term opctx ctx body ty =
  Coersion_termlang.force_typed_term @@ type_check opctx ctx body ty

let struc_infer_one opctx ctx x if_rec body =
  let rec get_fty e =
    match e.x with
    | Lam { lamarg; lambody } ->
        Sugar.(
          let* bty = get_fty lambody in
          let* aty = lamarg.ty in
          Some (Nt.Ty_arrow (aty, bty)))
    | _ -> e.ty
  in
  let res =
    match (if_rec, get_fty body) with
    | true, None ->
        _failatwith __FILE__ __LINE__ "require the return type of the function"
    | false, ty -> type_check opctx ctx body ty
    | true, Some ty ->
        type_check opctx NTypectx.(new_to_right ctx { x; ty }) body (Some ty)
  in
  res

let opt_to_typed_structure opctx ctx l =
  let () = NTypectx.pretty_print_lines ctx in
  let () = NOpTypectx.pretty_print_lines opctx in
  let l = map_imps (struc_infer_one opctx ctx) l in
  let l = map_rtys (Rtycheck.check opctx []) l in
  Coersion_structure.force_structure l
