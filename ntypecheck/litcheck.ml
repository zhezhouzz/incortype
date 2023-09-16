open Language
open Zzdatatype.Datatype
open Sugar
open LRaw
open Aux

let check opctx ctx (lit : lit typed) (ty : Nt.t) : lit typed =
  let rec type_infer ctx (lit : lit typed) : lit Nt.typed =
    match lit.ty with
    | Some ty -> Nt.{ x = (type_check ctx (lit, ty)).x; ty }
    | None -> (
        match lit.x with
        | AC c -> Nt.{ x = AC c; ty = infer_const_ty ctx c }
        | AVar x -> (
            try Nt.{ x = AVar x; ty = Ctx.find ctx x }
            with e ->
              Pp.printf
                "@{<bold>@{<red>Possible Reason:@} under return type should be \
                 locally closed.@}\n";
              raise e)
        | AEq _ ->
            Nt.{ x = (type_check ctx (lit, Nt.Ty_bool)).x; ty = Nt.Ty_bool }
        | AAppOp (f, args) ->
            let f, fty = check_op opctx f in
            let argsty, retty =
              _solve_by_argsty __FILE__ __LINE__ fty
                (List.map (fun x -> x.Nt.ty) (List.map (type_infer ctx) args))
            in
            let args =
              List.map (type_check ctx)
                (_safe_combine __FILE__ __LINE__ args argsty)
            in
            Nt.{ x = AAppOp (f, args); ty = retty })
  and type_check ctx (lit, ty) : lit typed =
    let _ =
      Env.show_debug_kw __FILE__ (fun _ ->
          Printf.printf "%s |- Check %s <<= %s\n" (layout_typectx ctx)
            (To_lit.layout_typed_lit lit)
            (Nt.layout ty))
    in
    let _ = _type_unify __FILE__ __LINE__ lit.ty (Some ty) in
    match lit.x with
    | AC _ | AVar _ ->
        let lit = type_infer ctx lit in
        let ty = _check_equality __FILE__ __LINE__ Nt.eq lit.Nt.ty ty in
        (* _unify_update __FILE__ __LINE__ ty lit *)
        lit.Nt.x #: (Some ty)
    | AEq (e1, e2) ->
        let _ = _check_equality __FILE__ __LINE__ Nt.eq ty Nt.bool_ty in
        let e1 = type_infer ctx e1 in
        let e2 = type_check ctx (e2, e1.Nt.ty) in
        (AEq (force_otyped e1, e2)) #: (Some Nt.bool_ty)
    | AAppOp (f, args) ->
        let f, fty = check_op opctx f in
        let argsty, retty =
          _solve_by_argsty __FILE__ __LINE__ fty
            (List.map (fun x -> x.Nt.ty) (List.map (type_infer ctx) args))
        in
        let argsty, retty =
          _solve_by_retty __FILE__ __LINE__
            (Nt.construct_arr_tp (argsty, retty))
            ty
        in
        let f = f.x #: (Some (Nt.construct_arr_tp (argsty, retty))) in
        let args =
          List.map (type_check ctx)
            (_safe_combine __FILE__ __LINE__ args argsty)
        in
        (AAppOp (f, args)) #: (Some retty)
  in
  type_check ctx (lit, ty)
