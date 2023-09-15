module MetaEnv = Env
open Ocaml5_parser
open Parsetree
open Pty
open Langlike
open Sugar
open Aux

let pprint_parn refinement_kind body =
  match refinement_kind with
  | Over -> spf "{%s}" body
  | Under -> spf "[%s]" body
  | Overlap -> spf "⟨%s⟩" body

let layout_stropt = function None -> "" | Some x -> spf "%s:" x
let layout_arr = function NormalArr -> "→" | GhostArr -> "⤏"

let rec layout pty =
  match pty with
  | PSingleRty tlit -> pprint_parn Overlap (To_lit.layout_lit tlit.x)
  | PBaseRty { refinement_kind; cty } ->
      pprint_parn refinement_kind (To_cty.pprint_cty cty)
  | PArrRty { arr_kind; rarg; retrty } ->
      spf "%s%s%s%s" (layout_stropt rarg.px) (layout rarg.pty)
        (layout_arr arr_kind) (layout retrty)

let kind_arr_of_ocaml pat =
  match pat.ppat_attributes with
  | [] -> NormalArr
  | [ a ] when String.equal a.attr_name.txt "ghost" -> GhostArr
  | _ -> _failatwith __FILE__ __LINE__ "die"

let refinement_kind_of_ocaml e =
  match e.pexp_attributes with
  | [] -> Overlap
  | [ a ] when String.equal a.attr_name.txt "over" -> Over
  | [ a ] when String.equal a.attr_name.txt "under" -> Under
  | [ a ] when String.equal a.attr_name.txt "incor" -> Overlap
  | _ -> _failatwith __FILE__ __LINE__ "die"

let rec mk_arrpty pattern ptyexpr body =
  let id = To_pat.patten_to_typed_ids pattern in
  let px =
    match id with
    | [ id ] when String.equal id.x "_" -> None
    | [ id ] -> Some id.x
    | _ -> failwith "pty_of_ocamlexpr_aux"
  in
  let arr_kind = kind_arr_of_ocaml pattern in
  let rarg = { px; pty = pty_of_ocamlexpr_aux ptyexpr } in
  let retrty = pty_of_ocamlexpr_aux body in
  PArrRty { arr_kind; rarg; retrty }

and pty_of_ocamlexpr_aux expr =
  let aux expr =
    match expr.pexp_desc with
    | Pexp_constraint _ -> (
        let refinement_kind = refinement_kind_of_ocaml expr in
        match vars_of_ocamlexpr expr with
        | [ _ ], _ ->
            PBaseRty { refinement_kind; cty = To_cty.cty_of_ocamlexpr expr }
        | [], e -> (
            let ONt.{ x; ty } = To_lit.typed_lit_of_ocamlexpr e in
            match ty with
            | None -> _failatwith __FILE__ __LINE__ "die"
            | Some ty -> PSingleRty Nt.{ x; ty })
        | _ -> _failatwith __FILE__ __LINE__ "die")
    | Pexp_fun (_, Some ptyexpr, pattern, body) ->
        mk_arrpty pattern ptyexpr body
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

let pty_of_ocamlexpr expr =
  let pty = pty_of_ocamlexpr_aux expr in
  let pty = unify_paras_pty pty in
  pty
