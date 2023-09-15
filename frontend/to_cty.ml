module MetaEnv = Env
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Syntax.RtyRaw.C
open Sugar
open Aux

let pprint_id Nt.{ x; ty } = spf "%s:%s" x (Nt.layout ty)
let pprint_id_name Nt.{ x; _ } = x

let pprint_cty { v; phi } =
  spf "%s | %s" (pprint_id v) @@ To_qualifier.layout phi

let cty_of_ocamlexpr expr =
  let cty =
    match vars_of_ocamlexpr expr with
    | [ v ], phi -> { v; phi = To_qualifier.qualifier_of_ocamlexpr phi }
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  normalize_name cty

let layout_cty = pprint_cty
let layout = pprint_cty
