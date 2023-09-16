open Langlike

module F (L : Lit.T) = struct
  open Sexplib.Std
  module P = Qualifier.F (L)
  include P
  open Zzdatatype.Datatype
  open Sugar

  type cty = { v : string Nt.typed; phi : prop } [@@deriving sexp]
  type 'a ctyped = { cx : 'a; cty : cty }

  let mk_unit_from_prop phi = { v = Nt.(v_name #: Ty_unit); phi }

  let cty_typed_to_prop { cx; cty } =
    match cty with
    | { v = { x; ty }; phi } -> (Nt.{ x = cx; ty }, P.subst (x, AVar cx) phi)

  let exists_xprop (x, xprop) cty =
    let v, phi = cty_typed_to_prop { cx = v_name; cty } in
    let phi = mk_exists x (smart_and [ xprop; phi ]) in
    { v; phi }

  let to_v_prop { v; phi } = (v, phi)

  let to_tlit_opt { v; phi } =
    let* { x; _ } = get_eq_by_name phi v.x in
    Some Nt.{ x; ty = v.ty }

  (* subst *)
  let subst (y, replacable) { v; phi } =
    if String.equal y v.x then { v; phi }
    else { v; phi = P.subst (y, replacable) phi }

  (* fv *)
  let fv { v; phi } =
    List.slow_rm_dup String.equal
    @@ List.filter (fun x -> not (String.equal x v.x))
    @@ P.fv phi

  (* erase *)

  let erase { v; _ } = v.ty

  (* normalize name *)

  let normalize_name { v; phi } =
    let phi = P.(subst (v.x, AVar v_name) phi) in
    let v = Nt.{ x = v_name; ty = v.ty } in
    { v; phi }

  (* union and intersect *)

  let union tau1 tau2 =
    let v, phi1 = to_v_prop tau1 in
    let _, phi2 = to_v_prop tau2 in
    { v; phi = smart_or [ phi1; phi2 ] }

  (* mk bot/top *)

  (* let mk_eq_lit v lit = *)
  (*   let ty : t = from_nt v.Nt.ty in *)
  (*   { v; phi = P.mk_teq v.Nt.ty v.Nt.x lit } *)

  let mk_bot nt = { v = Nt.(v_name #: nt); phi = mk_bool false }
  let mk_top nt = { v = Nt.(v_name #: nt); phi = mk_bool true }
end
