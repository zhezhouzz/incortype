open Sexplib.Std

type mode =
  | Debug of {
      show_preprocess : bool;
      show_typing : bool;
      show_queries : bool;
      show_solving : bool;
      show_stat : bool;
      show_info : bool;
      show_debug : bool;
      show_debug_kw : string list;
    }
  | Release
[@@deriving sexp]

type prim_path = (string * string) list [@@deriving sexp]

type meta_config = {
  mode : mode;
  max_printing_size : int;
  logfile : string;
  resfile : string;
  prim_path : prim_path;
}
[@@deriving sexp]

type config = { all_mps : string list; underp : string; measure : string }
[@@deriving sexp]

let meta_config : meta_config option ref = ref None
let config : config option ref = ref None

let get_meta () =
  match !meta_config with None -> failwith "uninit" | Some config -> config

let get_mode () = (get_meta ()).mode
let get_max_printing_size () = (get_meta ()).max_printing_size

let show_debug_kw kw (f : unit -> unit) =
  (* let () = Printf.printf "KW = %s\n" kw in *)
  match get_mode () with
  | Debug { show_debug_kw; _ } when List.exists (String.equal kw) show_debug_kw
    ->
      f ()
  | _ -> ()

let show_debug_preprocess (f : unit -> unit) =
  match get_mode () with
  | Debug { show_preprocess; _ } when show_preprocess -> f ()
  | _ -> ()

let show_debug_typing (f : unit -> unit) =
  match get_mode () with
  | Debug { show_typing; _ } when show_typing -> f ()
  | _ -> ()

let show_debug_queries (f : unit -> unit) =
  match get_mode () with
  | Debug { show_queries; _ } when show_queries -> f ()
  | _ -> ()

let show_debug_solving (f : unit -> unit) =
  match get_mode () with
  | Debug { show_solving; _ } when show_solving -> f ()
  | _ -> ()

let show_debug_stat (f : unit -> unit) =
  match get_mode () with
  | Debug { show_stat; _ } when show_stat -> f ()
  | _ -> ()

let show_debug_info (f : unit -> unit) =
  match get_mode () with
  | Debug { show_info; _ } when show_info -> f ()
  | _ -> ()

let show_debug_debug (f : unit -> unit) =
  match get_mode () with
  | Debug { show_debug; _ } when show_debug -> f ()
  | _ -> ()

let get_resfile () = (get_meta ()).resfile
let get_prim_path () = (get_meta ()).prim_path

let get_measure () =
  match !config with
  | None -> failwith "uninited prim path"
  | Some config -> config.measure

let get_path name =
  snd @@ List.find (fun (x, _) -> String.equal name x) (get_prim_path ())

open Yojson.Basic.Util

let load_meta meta_fname =
  (* let () = Printf.printf "meta_fname: %s\n" meta_fname in *)
  (* let () = Printf.printf "pwd: %s\n" (Sys.getcwd ()) in *)
  let metaj = Yojson.Basic.from_file meta_fname in
  let mode =
    match metaj |> member "mode" |> to_string with
    | "debug" ->
        (* let () = Pp.printf "@{<green>Verbose mode@}\n" in *)
        let get_bool field =
          metaj |> member "debug_info" |> member field |> to_bool
        in
        let get_kws () =
          metaj |> member "debug_info" |> member "debug_kw" |> to_list
          |> List.map to_string
        in
        Debug
          {
            show_preprocess = get_bool "show_preprocess";
            show_typing = get_bool "show_typing";
            show_queries = get_bool "show_queries";
            (* we don't need this field *)
            show_solving = false;
            show_stat = get_bool "show_stat";
            show_info = get_bool "show_info";
            show_debug = (try get_bool "show_debug" with _ -> false);
            show_debug_kw = (try get_kws () with _ -> []);
          }
    | "release" -> Release
    | _ -> failwith "config: unknown mode"
  in
  let max_printing_size = metaj |> member "max_printing_size" |> to_int in
  let resfile = metaj |> member "resfile" |> to_string in
  let logfile = metaj |> member "logfile" |> to_string in
  let p = metaj |> member "prim_path" in
  let prim_path = List.map (fun (x, y) -> (x, to_string y)) @@ to_assoc p in
  meta_config := Some { mode; max_printing_size; prim_path; logfile; resfile }
