module MetaEnv = Env
open Ocaml5_parser
open Parsetree
open Pty
open Langlike
open Aux
open Sugar

let pprint_parn refinement_kind body =
  match refinement_kind with
  | Over -> spf "{%s}" body
  | Under -> spf "[%s]" body
  | Overlap -> spf "⟨%s⟩" body

let layout_stropt = function None -> "" | Some x -> spf "%s:" x
let layout_arr = function NormalArr -> "→" | GhostArr -> "⤏"

let first_is_ghost pty =
  match pty with PArrRty { arr_kind = GhostArr; _ } -> true | _ -> false

let rec layout pty =
  match pty with
  | PSingleRty tlit -> pprint_parn Overlap (To_lit.layout_lit tlit.x)
  | PBaseRty { refinement_kind; cty } ->
      pprint_parn refinement_kind (To_cty.pprint_cty cty)
  | PArrRty { arr_kind; rarg; retrty } ->
      let rarg_pty = layout rarg.pty in
      let rarg_pty =
        if first_is_ghost rarg.pty then spf "(%s)" rarg_pty else rarg_pty
      in
      spf "%s%s%s%s" (layout_stropt rarg.px) rarg_pty (layout_arr arr_kind)
        (layout retrty)

let kind_arr_of_ocaml pat =
  match pat.ppat_attributes with
  | [] -> NormalArr
  | [ a ] when String.equal a.attr_name.txt "ghost" -> GhostArr
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
        let refinement_kind = refinement_kind_of_ocaml_v expr in
        (* let () = *)
        (*   Printf.printf "refinement_kind: %s\n" *)
        (*     (Sexplib.Sexp.to_string @@ sexp_of_refinement_kind *)
        (*    @@ refinement_kind) *)
        (* in *)
        let cty = To_cty.cty_of_ocamlexpr expr in
        match Syntax.RtyRaw.to_tlit_opt cty with
        | None ->
            PBaseRty { refinement_kind; cty = To_cty.cty_of_ocamlexpr expr }
        | Some tlit -> PSingleRty tlit)
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
  (* let () = Printf.printf "Parsed pty: %s\n" (layout pty) in *)
  pty
