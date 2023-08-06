open Core

let regular_file =
  Command.Arg_type.create (fun filename ->
      match Sys_unix.is_file filename with
      | `Yes -> filename
      | `No -> failwith "Not a regular file"
      | `Unknown -> failwith "Could not determine if this was a regular file")

let load_code_from_file qfile =
  let code = Ocaml5_parser.Frontend.parse ~sourcefile:qfile in
  let code = List.map ~f:To_structure.ocaml_structure_to_structure code in
  code

open Language

(* let load_ptys_from_file topnopctx code = *)
(*   let code = Ntypecheck.opt_to_typed_structure topnopctx [] code in *)
(*   let oprctx = POpTypectx.to_opctx @@ PTypectx.from_code code in *)
(*   oprctx *)

(* let load_erased_ntys_from_file code = *)
(*   let topnopctx = *)
(*     NOpTypectx.to_builtin @@ StructureRaw.mk_normal_top_ctx code *)
(*   in *)
(*   topnopctx *)
