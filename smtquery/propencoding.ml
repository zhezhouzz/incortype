open Z3
open Z3aux
open Language.Rty.P
(* open Sugar *)

let to_z3 ctx prop =
  let rec aux prop =
    match prop with
    | Lit lit -> Litencoding.typed_lit_to_z3 ctx lit #: Nt.bool_ty
    | Not p -> Boolean.mk_not ctx (aux p)
    | Ite (p1, p2, p3) -> Boolean.mk_ite ctx (aux p1) (aux p2) (aux p3)
    | Binary (Implies, p1, p2) -> Boolean.mk_implies ctx (aux p1) (aux p2)
    | Binary (Iff, p1, p2) -> Boolean.mk_iff ctx (aux p1) (aux p2)
    | Multi (And, ps) -> Boolean.mk_and ctx (List.map aux ps)
    | Multi (Or, ps) -> Boolean.mk_or ctx (List.map aux ps)
    | Qted (Fa, u, body) ->
        make_forall ctx [ tpedvar_to_z3 ctx (u.ty, u.x) ] (aux body)
    | Qted (Ex, u, body) ->
        make_exists ctx [ tpedvar_to_z3 ctx (u.ty, u.x) ] (aux body)
  in
  aux prop
