open Syntax
open Coersion_termlang
open Coersion_rty
module Raw = StructureRaw
open Structure

let force_entry entry =
  match entry with
  | Raw.Type_dec d -> Type_dec d
  | Raw.Func_dec d -> Func_dec d
  | Raw.FuncImp { name; if_rec; body } ->
      FuncImp { name; if_rec; body = force_typed_term body }
  | Raw.Rty { name; kind; rty } -> Rty { name; kind; rty = force rty }

let besome_entry entry =
  match entry with
  | Type_dec d -> Raw.Type_dec d
  | Func_dec d -> Raw.Func_dec d
  | FuncImp { name; if_rec; body } ->
      Raw.FuncImp { name; if_rec; body = besome_typed_term body }
  | Rty { name; kind; rty } -> Raw.Rty { name; kind; rty = besome rty }

let force_structure st = List.map force_entry st
let besome_structure st = List.map besome_entry st
