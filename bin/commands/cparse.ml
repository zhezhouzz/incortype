open Core
open Caux
open Language

let init_builtinctx () =
  let primop_nctx =
    StructureRaw.mk_normal_opctx @@ load_code_from_file
    @@ Env.get_path "builtin_normal_typing"
  in
  let primop_rctx =
    Structure.mk_rty_primopctx
    @@ Ntypecheck.opt_to_typed_structure primop_nctx []
    @@ load_code_from_file
    @@ Env.get_path "builtin_rty_typing"
  in
  (primop_nctx, primop_rctx)

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

let preprocess meta_config_file source_file =
  let primop_nctx, primop_rctx = init_builtinctx () in
  (* let () = Printf.printf "%s\n" (NOpTypectx.pretty_layout primop_nctx) in *)
  (* let () = Printf.printf "%s\n" (ROpTypectx.pretty_layout primop_rctx) in *)
  let source_code = load_code_from_file source_file in
  let librtys =
    Ntypecheck.opt_to_typed_structure primop_nctx []
    @@ StructureRaw.get_lib_rtys source_code
  in
  let rctx, nctx = Structure.mk_rty_ctx librtys in
  (* let () = Printf.printf "%s\n" (NTypectx.pretty_layout nctx) in *)
  (* let () = Printf.printf "%s\n" (RTypectx.pretty_layout rctx) in *)
  let source_code =
    Ntypecheck.opt_to_typed_structure primop_nctx nctx source_code
  in
  (* let () = Printf.printf "%s\n" @@ Structure.layout_structure source_code in *)
  let deccuried = Decurry.deccury_code source_code in
  let normalized = Normalize.get_normalized_code deccuried in
  let () =
    List.iter
      ~f:(fun (name, e) ->
        Pp.printf "%s:\n%s\n" name (Denormalize.layout_comp_omit_type e))
      normalized
  in
  let assertions = Structure.get_assert_rtys source_code in
  (rctx, normalized, assertions)

let test_parse meta_config_file source_file () =
  let rctx, normalized, assertions = preprocess meta_config_file source_file in
  ()

let test_subtyping meta_config_file source_file () =
  let rctx, normalized, assertions = preprocess meta_config_file source_file in
  let get x =
    snd @@ List.find_exn ~f:(fun (name, _) -> String.equal x name) assertions
  in
  let rty1 = get "rty1" in
  let rty2 = get "rty2" in
  let res = Subtyping.sub_rty_bool [] (rty1, rty2) in
  let () =
    Printf.printf "subtyping check\n%s\n<:\n%s\nresult: %b\n"
      (Rty.layout_rty rty1) (Rty.layout_rty rty2) res
  in
  ()

let test =
  Command.group ~summary:"Poirot"
    [
      ( "test-example",
        cmd_config "test init" (fun meta_config_file () ->
            let _ = Exset.Set.test () in
            ()) );
      ( "test-init",
        cmd_config "test init" (fun meta_config_file () ->
            let primop_nctx, primop_rctx = init_builtinctx () in
            let () =
              Printf.printf "%s\n" (NOpTypectx.pretty_layout primop_nctx)
            in
            let () =
              Printf.printf "%s\n" (ROpTypectx.pretty_layout primop_rctx)
            in
            ()) );
      ("test-parse", cmd_config_source "test parse" test_parse);
      ("test-subtyping", cmd_config_source "test subtyping" test_subtyping);
    ]
