module MetaEnv = Env
open Ocaml5_parser
open Parsetree

(* open Zzdatatype.Datatype *)
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Syntax.RtyRaw
open Sugar

let pprint_over_parn body = spf "{%s}" body
let pprint_under_parn body = spf "[%s]" body
let tpEvent str = spf "⟨%s⟩" str
let layout_stropt = function None -> "" | Some x -> spf "%s:" x
let layout_arr = function NormalArr -> "→" | GhostArr -> "⇢"

let rec pprint_rty rty =
  match rty with
  | BaseRty cty -> pprint_over_parn (To_cty.pprint_cty cty)
  | ArrRty { arr_kind; rarg; retrty } ->
      spf "%s%s%s%s" (layout_stropt rarg.ux) (pprint_uty rarg.uty)
        (layout_arr arr_kind) (pprint_rty retrty)

and pprint_uty = function
  | BaseUty cty -> pprint_under_parn (To_cty.pprint_cty cty)
  | ArrUty rty -> pprint_rty rty

(* let get_denoteopt_from_attr a = *)
(*   match a with [ x ] -> Some x.attr_name.txt | _ -> None *)

(* let get_denoteopt expr = get_denoteopt_from_attr expr.pexp_attributes *)

(* let get_denote expr = *)
(*   match get_denoteopt expr with *)
(*   | Some x -> x *)
(*   | None -> _failatwith __FILE__ __LINE__ "" *)

(* let get_opopt expr = *)
(*   match To_op.string_to_op (get_denote expr) with *)
(*   | Some (Op.DtOp op) -> Some op *)
(*   | _ -> None *)

(* let get_op expr = *)
(*   match get_opopt expr with *)
(*   | Some x -> x *)
(*   | None -> _failatwith __FILE__ __LINE__ "die" *)

(* let cty_of_ocamlexpr_aux expr = *)
(*   match vars_phi_of_ocamlexpr expr with *)
(*   | [ v ], phi -> { v; phi } *)
(*   | _ -> _failatwith __FILE__ __LINE__ "die" *)

let kind_arr_of_ocaml e =
  match e.pexp_attributes with
  | [] -> NormalArr
  | [ a ] when String.equal a.attr_name.txt "ghost" -> GhostArr
  | _ -> _failatwith __FILE__ __LINE__ "die"

let rec mk_arrrty pattern rtyexpr body =
  let id = To_pat.patten_to_typed_ids pattern in
  let ux =
    match id with
    | [ id ] when String.equal id.x "_" -> None
    | [ id ] -> Some id.x
    | _ -> failwith "rty_of_ocamlexpr_aux"
  in
  let arr_kind = kind_arr_of_ocaml rtyexpr in
  let rarg = ux #::: (uty_of_ocamlexpr_aux rtyexpr) in
  let retrty = rty_of_ocamlexpr_aux body in
  ArrRty { arr_kind; rarg; retrty }

and rty_of_ocamlexpr_aux expr =
  let aux expr =
    match expr.pexp_desc with
    | Pexp_constraint _ -> BaseRty (To_cty.cty_of_ocamlexpr expr)
    | Pexp_fun (_, Some rtyexpr, pattern, body) ->
        mk_arrrty pattern rtyexpr body
    | Pexp_fun _ ->
        _failatwith __FILE__ __LINE__
          (spf "wrong refinement type: %s"
             (Pprintast.string_of_expression expr))
    | _ ->
        _failatwith __FILE__ __LINE__
          (spf "wrong refinement type: %s"
             (Pprintast.string_of_expression expr))
  in
  aux expr

and uty_of_ocamlexpr_aux expr =
  match expr.pexp_desc with
  | Pexp_constraint _ -> BaseUty (To_cty.cty_of_ocamlexpr expr)
  | _ -> ArrUty (rty_of_ocamlexpr_aux expr)

let rty_of_ocamlexpr expr =
  let rty = rty_of_ocamlexpr_aux expr in
  let rty = normalize_name_rty rty in
  rty

let uty_of_ocamlexpr expr =
  let rty = uty_of_ocamlexpr_aux expr in
  let rty = normalize_name_uty rty in
  rty

let layout_rty = pprint_rty
let layout_uty = pprint_uty
