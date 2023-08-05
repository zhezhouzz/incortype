open Langlike

module F (L : Lit.T) = struct
  open Sexplib.Std
  module P = Qualifier.F (L)
  include P
  open Zzdatatype.Datatype

  type cty = { v : string Nt.typed; phi : prop } [@@deriving sexp]
  type 'a ctyped = { cx : 'a; cty : cty }

  let cty_typed_to_prop { cx; cty = { v = { x; ty }; phi } } =
    (Nt.{ x = cx; ty }, P.subst_id (x, cx) phi)

  (* subst *)
  let subst (y, replacable) { v; phi } =
    if String.equal y v.x then { v; phi }
    else { v; phi = P.subst (y, replacable) phi }

  let subst_id (y, z) = subst (y, AVar z)

  (* fv *)
  let fv { v; phi } =
    List.slow_rm_dup String.equal
    @@ List.filter (fun x -> String.equal x v.x)
    @@ P.fv phi

  (* erase *)

  let erase_cty { v; _ } = v.ty

  (* normalize name *)

  let normalize_name_cty { v; phi } =
    let phi = P.(subst_id (v.x, v_name) phi) in
    let v = Nt.{ x = v_name; ty = v.ty } in
    { v; phi }

  (* mk bot/top *)

  let mk_unit_from_prop phi = Nt.{ v = v_name #: Ty_unit; phi }

  let mk_eq_lit v lit =
    let ty : t = from_nt v.Nt.ty in
    { v; phi = P.mk_eq_lit { x = v.Nt.x; ty } lit }

  let mk_bot nt = Nt.{ v = v_name #: nt; phi = mk_bool false }
  let mk_top nt = Nt.{ v = v_name #: nt; phi = mk_bool true }
end
