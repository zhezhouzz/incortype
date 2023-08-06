open Langlike

module F (L : Lit.T) = struct
  open Sexplib.Std
  module P = Qualifier.F (L)
  include P
  open Zzdatatype.Datatype

  type cty =
    | ApprCty of { v : string Nt.typed; phi : prop }
    | EqCty of lit Nt.typed
  [@@deriving sexp]

  type 'a ctyped = { cx : 'a; cty : cty }

  let cty_typed_to_prop { cx; cty } =
    match cty with
    | ApprCty { v = { x; ty }; phi } ->
        (Nt.{ x = cx; ty }, P.subst (x, AVar cx) phi)
    | EqCty tlit ->
        let phi = P.mk_teq tlit.ty (AVar cx) tlit.x in
        let x = Nt.{ x = cx; ty = tlit.ty } in
        (x, phi)

  (* subst *)
  let subst (y, replacable) cty =
    match cty with
    | ApprCty { v; phi } ->
        if String.equal y v.x then cty
        else ApprCty { v; phi = P.subst (y, replacable) phi }
    | EqCty tlit ->
        if String.equal y v_name then cty
        else EqCty Nt.((L.subst (y, replacable)) #-> tlit)

  (* fv *)
  let fv = function
    | ApprCty { v; phi } ->
        List.slow_rm_dup String.equal
        @@ List.filter (fun x -> String.equal x v.x)
        @@ P.fv phi
    | EqCty tlit -> L.fv tlit.x

  (* erase *)

  let erase = function ApprCty { v; _ } -> v.ty | EqCty tlit -> tlit.ty

  (* normalize name *)

  let normalize_name = function
    | EqCty _ as cty -> cty
    | ApprCty { v; phi } -> (
        let phi = P.(subst (v.x, AVar v_name) phi) in
        let v = Nt.{ x = v_name; ty = v.ty } in
        match P.get_eq_by_name phi v_name with
        | None -> ApprCty { v; phi }
        | Some lit -> EqCty Nt.{ x = lit; ty = v.ty })

  (* mk bot/top *)

  let mk_unit_from_prop phi = ApprCty { v = Nt.(v_name #: Ty_unit); phi }

  (* let mk_eq_lit v lit = *)
  (*   let ty : t = from_nt v.Nt.ty in *)
  (*   { v; phi = P.mk_teq v.Nt.ty v.Nt.x lit } *)

  let mk_bot nt = ApprCty { v = Nt.(v_name #: nt); phi = mk_bool false }
  let mk_top nt = ApprCty { v = Nt.(v_name #: nt); phi = mk_bool true }
end
