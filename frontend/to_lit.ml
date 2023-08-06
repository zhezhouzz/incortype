module MetaEnv = Env
open Ocaml5_parser
open Parsetree
open Zzdatatype.Datatype
module Type = Normalty.Frontend
open Syntax
open StructureRaw
open LRaw
open Sugar

let f_proj = "proj"

let rec lit_to_ocamlexpr expr =
  To_expr.desc_to_ocamlexpr @@ lit_to_ocamlexpr_desc expr

and typed_lit_to_ocamlexpr expr =
  To_expr.desc_to_ocamlexpr @@ typed_lit_to_ocamlexpr_desc expr

and typed_lit_to_ocamlexpr_desc expr = lit_to_ocamlexpr_desc expr.x

and lit_to_ocamlexpr_desc (expr : lit) =
  let aux expr =
    match expr with
    | AC c -> (To_const.value_to_expr c).pexp_desc
    | AAppOp (op, args) ->
        let op = To_expr.typed_op_to_ocamlexpr op.x #: None in
        let args =
          List.map (fun x -> (Asttypes.Nolabel, typed_lit_to_ocamlexpr x)) args
        in
        Pexp_apply (op, args)
    | AEq (l1, l2) ->
        let l1 = (Asttypes.Nolabel, typed_lit_to_ocamlexpr l1) in
        let l2 = (Asttypes.Nolabel, typed_lit_to_ocamlexpr l2) in
        let op =
          To_expr.typed_op_to_ocamlexpr @@ ((Op.BuiltinOp "==") #: None)
        in
        Pexp_apply (op, [ l1; l2 ])
    | AVar x -> (To_expr.id_to_ocamlexpr x).pexp_desc
  in
  aux expr

let layout_lit lit = Pprintast.string_of_expression @@ lit_to_ocamlexpr lit
let layout_typed_lit lit = layout_lit lit.x

let rec term_to_lit expr =
  (fun e ->
    match e with
    | Const c -> AC c
    | Var id -> AVar id
    | AppOp (op, args) -> (
        let args = List.map term_to_lit args in
        match (op.x, args) with
        | Op.BuiltinOp "==", [ a; b ] -> AEq (a, b)
        | Op.BuiltinOp "==", _ -> _failatwith __FILE__ __LINE__ "?"
        | _, _ -> AAppOp (op, args))
    | App (op, args) ->
        let op =
          match op.x with
          | Var id -> { x = Op.BuiltinOp id; ty = op.ty }
          | _ ->
              _failatwith __FILE__ __LINE__
              @@ spf "parsing: not a op (%s)"
              @@ To_expr.layout expr
        in
        AAppOp (op, List.map term_to_lit args)
    | _ ->
        _failatwith __FILE__ __LINE__
        @@ spf "parsing: not a op (%s)"
        @@ To_expr.layout expr)
  #-> expr

let typed_lit_of_ocamlexpr e = term_to_lit (To_expr.expr_of_ocamlexpr e)
let lit_of_ocamlexpr e = (typed_lit_of_ocamlexpr e).x
