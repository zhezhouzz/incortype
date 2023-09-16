module MetaEnv = Env
open Ocaml5_parser
open Parsetree
module Type = Normalty.Frontend
open Syntax
open RtyRaw.P
open Sugar
open Aux

let quantifier_to_patten (q, u) =
  To_pat.dest_to_pat
    (Ppat_constraint
       ( To_pat.dest_to_pat (Ppat_var (Location.mknoloc u.Nt.x)),
         notated (Connective.qt_to_string q, u.Nt.ty) ))

open Zzdatatype.Datatype

let rec qualifier_to_ocamlexpr expr =
  To_expr.desc_to_ocamlexpr @@ qualifier_to_ocamlexpr_desc expr

and qualifier_to_ocamlexpr_desc expr =
  let rec aux e =
    let labeled x = (Asttypes.Nolabel, qualifier_to_ocamlexpr x) in
    match e with
    | Lit lit -> To_lit.lit_to_ocamlexpr_desc lit
    | Ite (e1, e2, e3) ->
        Pexp_ifthenelse
          ( qualifier_to_ocamlexpr e1,
            qualifier_to_ocamlexpr e2,
            Some (qualifier_to_ocamlexpr e3) )
    | Not e -> Pexp_apply (To_expr.id_to_ocamlexpr "not", List.map labeled [ e ])
    | Binary (binary, e1, e2) ->
        let binary = match binary with Implies -> "implies" | Iff -> "iff" in
        Pexp_apply (To_expr.id_to_ocamlexpr binary, List.map labeled [ e1; e2 ])
    | Multi (multi, es) -> (
        match es with
        | [] -> failwith "un-imp"
        | [ x ] -> aux x
        | h :: t ->
            Pexp_apply
              ( To_expr.id_to_ocamlexpr
                  (match multi with And -> "&&" | Or -> "||"),
                List.map labeled [ h; Multi (multi, t) ] ))
    | Qted (qt, u, body) ->
        Pexp_fun
          ( Asttypes.Nolabel,
            None,
            quantifier_to_patten (qt, u),
            qualifier_to_ocamlexpr body )
  in
  aux expr

let quantifier_of_ocamlexpr arg =
  match arg.ppat_desc with
  | Ppat_constraint (arg, ct) -> (
      let arg =
        match arg.ppat_desc with
        | Ppat_var arg -> arg.txt
        | _ -> failwith "parsing: prop function"
      in
      match ct.ptyp_desc with
      | Ptyp_extension (name, PTyp ty) ->
          let q = Connective.qt_of_string name.txt in
          let ty = Type.core_type_to_t ty in
          (q, Nt.(arg #: ty))
      | _ -> _failatwith __FILE__ __LINE__ "quantifier needs type extension")
  | _ -> _failatwith __FILE__ __LINE__ "quantifier needs type notation"

let qualifier_of_ocamlexpr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_constraint _ -> failwith "parsing: qualifier does not have type"
    | Pexp_let _ -> failwith "parsing: qualifier does not have let"
    | Pexp_match _ -> failwith "parsing: qualifier does not have match"
    | Pexp_apply (func, args) -> (
        let f = To_expr.id_of_ocamlexpr func in
        let args = List.map snd args in
        match (f, args) with
        | "not", [ e1 ] -> Not (aux e1)
        | "not", _ -> failwith "parsing: qualifier wrong not"
        | "ite", [ e1; e2; e3 ] -> Ite (aux e1, aux e2, aux e3)
        | "ite", _ -> failwith "parsing: qualifier wrong ite"
        | "implies", [ e1; e2 ] -> Binary (Implies, aux e1, aux e2)
        | "implies", _ -> failwith "parsing: qualifier wrong implies"
        | "iff", [ e1; e2 ] -> Binary (Iff, aux e1, aux e2)
        | "iff", _ -> failwith "parsing: qualifier wrong iff"
        | "&&", [ a; b ] -> Multi (And, [ aux a; aux b ])
        | "&&", _ -> failwith "parsing: qualifier wrong and"
        | "||", [ a; b ] -> Multi (Or, [ aux a; aux b ])
        | "||", _ -> failwith "parsing: qualifier wrong or"
        | "=", _ -> failwith "please use == instead of ="
        | _, _ -> Lit (To_lit.lit_of_ocamlexpr expr))
    | Pexp_ifthenelse (e1, e2, Some e3) -> Ite (aux e1, aux e2, aux e3)
    | Pexp_ifthenelse (_, _, None) -> raise @@ failwith "no else branch in ite"
    | Pexp_fun (_, _, arg, expr) ->
        let q, arg = quantifier_of_ocamlexpr arg in
        Qted (q, arg, aux expr)
    | Pexp_tuple _ | Pexp_ident _ | Pexp_constant _ | Pexp_construct _ ->
        Lit (To_lit.lit_of_ocamlexpr expr)
    | _ ->
        raise
        @@ failwith
             (spf "not imp client parsing:%s"
             @@ Pprintast.string_of_expression expr)
  in
  aux expr

open To_connective

module F (S : S) = struct
  open S

  let rec layout = function
    | Lit (AC (Const.B true)) -> sym_true
    | Lit (AC (Const.B false)) -> sym_false
    | Lit lit -> To_lit.layout_lit lit
    | Not p -> spf "%s(%s)" sym_not @@ layout p
    | Ite (p1, p2, p3) ->
        spf "(if %s then %s else %s)" (layout p1) (layout p2) (layout p3)
    | Binary (binary, p1, p2) ->
        spf "(%s %s %s)" (layout p1) (layout_binary binary) (layout p2)
    | Multi (_, []) -> _failatwith __FILE__ __LINE__ "die"
    | Multi (_, [ x ]) -> layout x
    | Multi (multi, [ p1; p2 ]) ->
        spf "(%s %s %s)" (layout p1) (layout_multi multi) (layout p2)
    | Multi (multi, ps) ->
        spf "(%s)" @@ List.split_by (layout_multi multi) layout ps
    | Qted (qt, u, body) ->
        spf "(%s%s. %s)" (layout_qt qt) (layout_typedid u) (layout body)
end

module DetailsLayout = F (DetailsS)
module PpLayout = F (PpS)
module CoqLayout = F (CoqS)

let layout_lit = To_lit.layout_lit
let layout_typed_lit = To_lit.layout_typed_lit
let layout_raw x = Pprintast.string_of_expression @@ qualifier_to_ocamlexpr x
let layout = PpLayout.layout
