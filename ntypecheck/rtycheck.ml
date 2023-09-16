open Language
module Typectx = NTypectx
open Sugar
open RtyRaw

let check opctx ctx (rty : rty) : rty =
  let rec aux ctx rty =
    match rty with
    | SingleRty lit ->
        let lit =
          Aux.force_typed @@ Litcheck.check opctx ctx lit.Nt.x #: None lit.Nt.ty
        in
        SingleRty lit
    | BaseRty { cty } -> BaseRty { cty = Ctycheck.check opctx ctx cty }
    | ArrRty { arr_kind; rarg; retrty } ->
        let rarg = { rx = rarg.rx; rty = aux ctx rarg.rty } in
        let () =
          match rarg.rx with
          | None ->
              _assert __FILE__ __LINE__
                (spf "syntax error: argument type %s" (To_rty.layout rty))
              @@ (is_arr rarg.rty || is_base rarg.rty)
          | Some _ -> ()
          (* _assert __FILE__ __LINE__ "syntax error: argument type" *)
          (* @@ is_base_pty rarg.rty *)
        in
        let ctx' =
          match rarg.rx with
          | None -> ctx
          | Some x -> Typectx.new_to_right ctx Nt.(x #: (erase_rty rarg.rty))
        in
        ArrRty { arr_kind; rarg; retrty = aux ctx' retrty }
  in
  aux ctx rty
