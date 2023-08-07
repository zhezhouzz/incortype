module MetaEnv = Env
open Ocaml5_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Syntax.RtyRaw.C
open Sugar

let pprint_id Nt.{ x; ty } = spf "%s:%s" x (Nt.layout ty)
let pprint_id_name Nt.{ x; _ } = x

let pprint_cty = function
  | EqCty x -> To_lit.layout_lit x.x
  | ApprCty { v; phi } -> spf "%s | %s" (pprint_id v) @@ To_qualifier.layout phi

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

let cty_of_ocamlexpr expr =
  let cty =
    match vars_of_ocamlexpr expr with
    | [ v ], phi -> ApprCty { v; phi = To_qualifier.qualifier_of_ocamlexpr phi }
    | [], e -> (
        let { x; ty } = To_lit.typed_lit_of_ocamlexpr e in
        match ty with
        | None -> _failatwith __FILE__ __LINE__ "die"
        | Some ty -> EqCty Nt.{ x; ty })
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  normalize_name cty

let layout_cty = pprint_cty
let layout = pprint_cty
