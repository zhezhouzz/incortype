open Syntax
module Raw = RtyRaw
open Rty

let force qualifier =
  let rec aux qualifier =
    match qualifier with
    | Raw.Lit qualifier -> Lit (Coersion_lit.force qualifier)
    | Raw.Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
    | Raw.Not e -> Not (aux e)
    | Raw.Binary (binary, e1, e2) -> Binary (binary, aux e1, aux e2)
    | Raw.Multi (multi, es) -> Multi (multi, List.map aux es)
    | Raw.Qted (qt, u, e) -> Qted (qt, u, aux e)
  in
  aux qualifier

let besome qualifier =
  let rec aux qualifier =
    match qualifier with
    | Lit lit -> Raw.Lit (Coersion_lit.besome lit)
    | Not e -> Raw.Not (aux e)
    | Ite (e1, e2, e3) -> Raw.Ite (aux e1, aux e2, aux e3)
    | Binary (binary, e1, e2) -> Raw.Binary (binary, aux e1, aux e2)
    | Multi (m, es) -> Raw.Multi (m, List.map aux es)
    | Qted (qt, u, e) -> Raw.Qted (qt, u, aux e)
  in
  aux qualifier
