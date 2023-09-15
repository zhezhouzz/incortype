open Language
module T = Structure
open TypedCore

(* open Sugar *)
open Zzdatatype.Datatype

let rec denormalize_comp (comp : comp typed) : T.term T.typed =
  let compty = comp.ty in
  let res =
    match comp.x with
    | CVal v -> T.((denormalize_value v #: compty).x)
    | CMatch { matched; match_cases } ->
        T.(
          Match
            ( denormalize_value matched,
              List.map denormalize_match_case match_cases ))
    | CLet { lhs; rhs; letbody } ->
        T.(
          Let
            {
              if_rec = false;
              lhs = [ lhs ];
              rhs = denormalize_rhs rhs;
              letbody = denormalize_comp letbody;
            })
  in
  T.(res #: compty)

and denormalize_rhs (rhs : rhs typed) : T.term T.typed =
  let compty = rhs.ty in
  let res =
    match rhs.x with
    | CErr -> T.Err
    | CRhsV v -> T.((denormalize_value v #: compty).x)
    | CApp { appf; apparg } ->
        T.(App (denormalize_value appf, [ denormalize_value apparg ]))
    | CAppOp { op; appopargs } ->
        T.(AppOp (op, List.map denormalize_value appopargs))
  in
  T.(res #: compty)

and denormalize_value (value : value typed) : T.term T.typed =
  let valuety = value.ty in
  let res =
    match value.x with
    | VVar name -> T.Var name
    | VConst const -> T.Const const
    | VLam { lamarg; lambody } ->
        T.(Lam { lamarg; lambody = denormalize_comp lambody })
    | VFix { fixname; fixarg; fixbody } ->
        let open T in
        let lambody =
          (Lam { lamarg = fixarg; lambody = denormalize_comp fixbody })
          #: valuety
        in
        Lam { lamarg = fixname; lambody }
  in
  T.(res #: valuety)

and denormalize_match_case { constructor; args; exp } : T.match_case =
  T.{ constructor; args; exp = denormalize_comp exp }

let layout_comp comp = T.layout_term (denormalize_comp comp)
let layout_value comp = T.layout_term (denormalize_value comp)
let layout_comp_omit_type comp = T.layout_term_omit_type (denormalize_comp comp)

let layout_value_omit_type comp =
  T.layout_term_omit_type (denormalize_value comp)
