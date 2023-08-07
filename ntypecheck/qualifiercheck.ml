open Language
open Zzdatatype.Datatype
open RtyRaw.P

let check opctx ctx (qualifier : prop) : prop =
  let rec aux ctx qualifier =
    match qualifier with
    | Lit lit -> Lit (Litcheck.check opctx ctx lit #: None Nt.Ty_bool).x
    | Ite (e1, e2, e3) -> Ite (aux ctx e1, aux ctx e2, aux ctx e3)
    | Not e -> Not (aux ctx e)
    | Binary (binary, e1, e2) -> Binary (binary, aux ctx e1, aux ctx e2)
    | Multi (multi, es) -> Multi (multi, List.map (aux ctx) es)
    | Qted (qt, u, body) -> Qted (qt, u, aux (NTypectx.new_to_right ctx u) body)
  in
  aux ctx qualifier
