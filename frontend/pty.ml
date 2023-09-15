(* open Zzdatatype.Datatype *)
module Type = Normalty.Frontend
module Nt = Normalty.Ntyped
open Syntax.RtyRaw
open Sugar
open Sexplib.Std
open Langlike

type pty =
  | PSingleRty of lit Nt.typed  (** singlton type *)
  | PBaseRty of { refinement_kind : refinement_kind; cty : cty }
  | PArrRty of {
      arr_kind : arr_kind;
      rarg : string option ptyped;
      retrty : pty;
    }

and 'a ptyped = { px : 'a; pty : pty } [@@deriving sexp]

let flip_para = function
  | PSingleRty _ -> _failatwith __FILE__ __LINE__ "die"
  | PBaseRty { refinement_kind = Overlap; cty } ->
      PBaseRty { refinement_kind = Over; cty }
  | _ as pty -> pty

let unify_paras_pty pty =
  match pty with
  | PBaseRty _ | PSingleRty _ -> pty
  | PArrRty { arr_kind; rarg; retrty } ->
      let rarg = { px = rarg.px; pty = flip_para rarg.pty } in
      PArrRty { arr_kind; rarg; retrty }

let rec destruct_normal_arr_ptyopt rty =
  match rty with
  | PBaseRty _ | PSingleRty _ -> Some ([], rty)
  | PArrRty { arr_kind = NormalArr; rarg; retrty } ->
      let* parartys, retrty = destruct_normal_arr_ptyopt retrty in
      Some (rarg :: parartys, retrty)
  | PArrRty { arr_kind = GhostArr; _ } -> None

let rec destruct_arr_ptyopt rty =
  match rty with
  | PBaseRty _ | PSingleRty _ -> Some ([], [], rty)
  | PArrRty { arr_kind = NormalArr; _ } ->
      let* parartys, retrty = destruct_normal_arr_ptyopt rty in
      Some ([], parartys, retrty)
  | PArrRty { arr_kind = GhostArr; rarg; retrty } -> (
      let* gparartys, parartys, retrty = destruct_arr_ptyopt retrty in
      match (rarg.px, rarg.pty) with
      | Some x, PBaseRty { refinement_kind = Over; cty } ->
          Some ((x, cty) :: gparartys, parartys, retrty)
      | _, _ -> _failatwith __FILE__ __LINE__ "die")

let reconstruct_pty (gparas, paras, retty) =
  let res =
    List.fold_right
      (fun rarg retrty -> PArrRty { arr_kind = NormalArr; rarg; retrty })
      paras retty
  in
  let res =
    List.fold_right
      (fun (x, cty) retrty ->
        PArrRty
          {
            arr_kind = GhostArr;
            rarg =
              { px = Some x; pty = PBaseRty { refinement_kind = Over; cty } };
            retrty;
          })
      gparas res
  in
  res

let rec fv_pty rty =
  match rty with
  | PSingleRty tlit -> Lit.LitRaw.fv tlit.x
  | PBaseRty { cty; _ } -> C.fv cty
  | PArrRty { rarg; retrty; _ } ->
      let argfv = fv_pty rarg.pty in
      let retfv = fv_pty retrty in
      let retfv =
        match rarg.px with
        | None -> retfv
        | Some x -> Zzdatatype.Datatype.List.remove_elt String.equal x retfv
      in
      argfv @ retfv

let rec rty_to_pty rty =
  let gparas, paras, retty = destruct_arr_rty rty in
  let paras =
    List.map (fun { rx; rty } -> { px = rx; pty = rty_to_pty rty }) paras
  in
  let gparas, retty =
    match (gparas, retty) with
    | (x, cty) :: gparas, SingleRty { x = Syntax.LRaw.AVar y; ty } ->
        (* let dummy_ret = *)
        (*   PBaseRty { refinement_kind = Overlap; cty = C.mk_bot Nt.int_ty } *)
        (* in *)
        (* let dummy_pty = reconstruct_pty (gparas, paras, dummy_ret) in *)
        if String.equal x y then
          ((x, cty) :: gparas, PBaseRty { refinement_kind = Overlap; cty })
        else (gparas, PSingleRty { x = Syntax.LRaw.AVar y; ty })
    | _, BaseRty { cty } -> (gparas, PBaseRty { refinement_kind = Overlap; cty })
    | _, _ -> _failatwith __FILE__ __LINE__ "die"
  in
  reconstruct_pty (gparas, paras, retty)

let rec pty_to_rty pty =
  let gparas, paras, retty =
    match destruct_arr_ptyopt pty with
    | Some (a, b, c) -> (a, b, c)
    | None -> failwith "refinement type parsing error"
  in
  let paras =
    List.map (fun { px; pty } -> { rx = px; rty = pty_to_rty pty }) paras
  in
  let gparas, retty =
    match retty with
    | PSingleRty tlit -> (gparas, SingleRty tlit)
    | PBaseRty { refinement_kind = Under; cty } ->
        let retname = Rename.unique "ret" in
        let retty = SingleRty Nt.((C.AVar retname) #: cty.v.ty) in
        ((retname, cty) :: gparas, retty)
    | PBaseRty { refinement_kind = Overlap; cty } -> (gparas, BaseRty { cty })
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  reconstruct_rty (gparas, paras, retty)
