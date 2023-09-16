module MetaEnv = Env
open Ocaml5_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Langlike
open Syntax.RtyRaw.C
open Sugar

let refinement_kind_of_attributes attr =
  match attr with
  | [] -> Overlap
  | [ a ] when String.equal a.attr_name.txt "over" -> Over
  | [ a ] when String.equal a.attr_name.txt "under" -> Under
  | [ a ] when String.equal a.attr_name.txt "incor" -> Overlap
  | _ -> _failatwith __FILE__ __LINE__ "die"

let refinement_kind_of_ocaml e = refinement_kind_of_attributes e.pexp_attributes

let refinement_kind_of_ocaml_v expr =
  match expr.pexp_desc with
  | Pexp_constraint (_, ct) -> refinement_kind_of_attributes ct.ptyp_attributes
  | _ -> _failatwith __FILE__ __LINE__ "die"

let get_self ct =
  let open Nt in
  match ct.ptyp_desc with
  | Ptyp_extension (name, PTyp ty) -> name.txt #: (Type.core_type_to_t ty)
  | _ ->
      let () = Printf.printf "\nct: %s\n" (layout_coretype ct) in
      _failatwith __FILE__ __LINE__ ""

let vars_of_ocamlexpr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_constraint (e', ct) ->
        let v = get_self ct in
        let vs, phi = aux e' in
        (v :: vs, phi)
    | _ -> ([], expr)
  in
  let vs, prop = aux expr in
  (List.rev vs, prop)

let typed_to_ocamlexpr_desc f expr =
  match expr.ty with
  | None -> f expr.x
  | Some ty ->
      Pexp_constraint
        (To_expr.desc_to_ocamlexpr @@ f expr.x, Type.t_to_core_type ty)

let notated (name, t) =
  Type.desc_to_ct
  @@ Ptyp_extension (Location.mknoloc name, PTyp (Type.t_to_core_type t))
