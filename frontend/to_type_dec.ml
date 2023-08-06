open Ocaml5_parser
open Parsetree
open Syntax.Type_dec
module Type = Normalty.Frontend

let sig_desc_to_sig e = { psig_desc = e; psig_loc = Location.none }

let constructor_declaration_of_ocaml { pcd_name; pcd_args; _ } =
  let argsty =
    match pcd_args with
    | Pcstr_tuple cts -> List.map Type.core_type_to_t cts
    | _ -> failwith "unimp complex type decl"
  in
  { constr_name = pcd_name.txt; argsty }

let constructor_declaration_to_ocaml { constr_name; argsty } =
  {
    pcd_name = Location.mknoloc constr_name;
    pcd_vars = [];
    pcd_args = Pcstr_tuple (List.map Type.t_to_core_type argsty);
    pcd_res = None;
    pcd_loc = Location.none;
    pcd_attributes = [];
  }

let of_ocamldec { ptype_name; ptype_params; ptype_kind; ptype_manifest; _ } =
  match (ptype_params, ptype_kind, ptype_manifest) with
  | params, Ptype_variant cds, None ->
      let type_params =
        List.map (fun (ct, (_, _)) -> Type.core_type_to_t ct) params
      in
      {
        type_name = ptype_name.txt;
        type_params;
        type_decls = List.map constructor_declaration_of_ocaml cds;
      }
  | _ -> failwith "unimp complex type decl"

(* open Sugar *)

let to_ocamldec e =
  match e with
  | { type_name; type_params; type_decls } ->
      let dec =
        {
          ptype_name = Location.mknoloc type_name;
          ptype_params =
            List.map
              (fun t ->
                ( Type.t_to_core_type t,
                  (Asttypes.NoVariance, Asttypes.NoInjectivity) ))
              type_params;
          ptype_cstrs = [];
          ptype_kind =
            Ptype_variant (List.map constructor_declaration_to_ocaml type_decls);
          ptype_manifest = None;
          ptype_attributes = [];
          ptype_loc = Location.none;
          ptype_private = Asttypes.Public;
        }
      in
      dec

let to_ocamlsig e =
  let desc = Psig_type (Asttypes.Nonrecursive, [ to_ocamldec e ]) in
  sig_desc_to_sig desc

let layout e =
  let _ = Format.flush_str_formatter () in
  Pprintast.signature Format.str_formatter (List.map to_ocamlsig e);
  Format.flush_str_formatter ()
