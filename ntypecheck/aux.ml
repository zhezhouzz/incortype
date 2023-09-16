open Language

(* open Const *)
module Ctx = NTypectx
module OpCtx = NOpTypectx

(* open Nt *)
open Sugar

let is_builtop opctx x = OpCtx.exists opctx (Op.BuiltinOp x)
let infer_const_ty _ = Const.infer_const_ty

let infer_op opctx x =
  match x with
  | Op.BuiltinOp _ -> OpCtx.find opctx x
  | Op.DtOp x ->
      let x = Printf.sprintf "_%s" x in
      OpCtx.find opctx (Op.BuiltinOp x)
(* ( *)
(*   match x with *)
(*   | "S" -> Ty_arrow (Ty_int, Ty_int) *)
(*   | _ -> *)
(*       _failatwith __FILE__ __LINE__ *)
(*       @@ spf "cannot infer the basic type of %s" x) *)

open ONt
open Zzdatatype.Datatype

let layout_typectx ctx =
  List.split_by_comma (fun (x, ty) -> spf "%s:%s" x @@ Nt.layout ty) ctx

let _unify = _type_unify
let _unify_ = Nt._type_unify_

let _unify_update file line ty' { x; ty } =
  x #: (_unify file line ty (Some ty'))

let check_id nctx (x : string typed) : string typed * Nt.t =
  let ty = Ctx.find nctx x.x in
  (_unify_update __FILE__ __LINE__ ty x, ty)

let check_op opctx (x : Op.t typed) : Op.t typed * Nt.t =
  let ty = infer_op opctx x.x in
  (_unify_update __FILE__ __LINE__ ty x, ty)

let force_typed { x; ty } =
  match ty with
  | None -> _failatwith __FILE__ __LINE__ "?"
  | Some ty -> Nt.{ x; ty }

let force_otyped Nt.{ x; ty } = { x; ty = Some ty }

let _solve_by_retty file line fty retty' =
  let open Nt in
  let argsty, retty = destruct_arr_tp fty in
  let m, retty = _unify_ file line StrMap.empty retty retty' in
  let subst m t =
    let rec aux t =
      match t with
      | Ty_var n -> (
          match StrMap.find_opt m n with None -> t | Some ty -> ty)
      | Ty_arrow (t1, t2) -> Ty_arrow (aux t1, aux t2)
      | Ty_tuple ts -> Ty_tuple (List.map aux ts)
      | Ty_constructor (id, ts) -> Ty_constructor (id, List.map aux ts)
      | _ -> t
    in
    aux t
  in
  let argsty = List.map (subst m) argsty in
  (argsty, retty)

let _solve_by_argsty file line fty argsty' =
  let open Nt in
  let argsty, retty = destruct_arr_tp fty in
  let m, argsty_ =
    _type_unify_ file line StrMap.empty (mk_tuple argsty) (mk_tuple argsty')
  in
  let argsty = match argsty_ with Ty_tuple argsty -> argsty | t -> [ t ] in
  let retty = subst_m m retty in
  (argsty, retty)
