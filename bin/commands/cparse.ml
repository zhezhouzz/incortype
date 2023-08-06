open Core
open Caux
open Language

let init_builtinctx () =
  let primop_nctx =
    StructureRaw.mk_normal_opctx @@ load_code_from_file
    @@ Env.get_path "builtin_normal_typing"
  in
  primop_nctx

let cmd_config summary f =
  Command.basic ~summary
    Command.Let_syntax.(
      let%map_open meta_config_file =
        anon ("meta_config_file" %: regular_file)
      in
      let () = Env.load_meta meta_config_file in
      f meta_config_file)

let cmd_config_source summary f =
  Command.basic ~summary
    Command.Let_syntax.(
      let%map_open meta_config_file = anon ("meta_config_file" %: regular_file)
      and source_file = anon ("source_code_file" %: regular_file) in
      let () = Env.load_meta meta_config_file in
      f meta_config_file source_file)

let test =
  Command.group ~summary:"Poirot"
    [
      ( "test-init",
        cmd_config "test init" (fun meta_config_file () ->
            let primop_nctx = init_builtinctx () in
            let () =
              Printf.printf "%s\n" (NOpTypectx.pretty_layout primop_nctx)
            in
            ()) );
    ]
