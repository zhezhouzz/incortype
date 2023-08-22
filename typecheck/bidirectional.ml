open Language
open TypedCore
open Rty
open Sugar
open Typeerr
open Typingaux

let print_term_type_syn (ctx : Type_ctx.t) (e : comp typed) =
  let open Type_ctx in
  Env.show_debug_typing (fun _ ->
      let () = Pp.printf "@{<bold>Type Synthesize:@}\n" in
      pretty_print ctx;
      Pp.printf "\n⊢ @{<hi_magenta>%s@} ⇨ "
        (short_str 10000
           (TypedCore.layout_term (Denormalize.denormalize_comp e)));
      Pp.printf "@{<cyan>?@}\n\n")

let print_value_type_syn (ctx : Type_ctx.t) (v : value typed) =
  print_term_type_syn ctx (CVal v.x) #: v.ty

let print_term_type_check (ctx : Type_ctx.t) (e : comp typed) (tau : rty) =
  let open Type_ctx in
  Env.show_debug_typing (fun _ ->
      let () = Pp.printf "@{<bold>Type Check:@}\n" in
      pretty_print ctx;
      Pp.printf "\n⊢ @{<hi_magenta>%s@} ⇦ "
        (short_str 10000
           (TypedCore.layout_term (Denormalize.denormalize_comp e)));
      Pp.printf "@{<cyan>%s@}\n\n" (layout_rty tau))

let print_value_type_check (ctx : Type_ctx.t) (v : value typed) (tau : rty) =
  print_term_type_check ctx (CVal v.x) #: v.ty tau

let rec value_type_check (ctx : Type_ctx.t) (v : value typed) (tau : rty) :
    (Type_ctx.t * rty) typing_result =
  let () = print_value_type_check ctx v tau in
  let ctx, tau = handle_ghost ctx tau in
  match (v.x, tau) with
  | _, ArrRty { arr_kind = GhostArr; _ } -> _failatwith __FILE__ __LINE__ "die"
  | VConst _, _ ->
      let* ctx, syned_tau = value_type_syn ctx v in
      let _ = subtyping_check ctx (syned_tau, tau) in
      TypeSuccess (ctx, tau)
  | VVar x, _ ->
      let* ctx, syned_tau = value_type_syn ctx v in
      let _ = subtyping_check ctx (syned_tau, tau) in
      let ctx = Type_ctx.consume_from_ctx ctx (x, tau) in
      TypeSuccess (ctx, tau)
  | VLam { lamarg; lambody }, ArrRty { arr_kind = NormalArr; rarg; retrty } ->
      let ctx = Type_ctx.new_to_ctx ctx (lamarg.x, rarg.rty) in
      let retrty =
        match rarg.rx with
        | None -> retrty
        | Some x -> rty_subst_value (x, VVar lamarg.x) retrty
      in
      term_type_check ctx lambody retrty
  | VFix { fixname; fixarg; fixbody }, ArrRty { arr_kind = NormalArr; _ } ->
      let ctx = Type_ctx.new_to_ctx ctx (fixname.x, tau) in
      let v = VLam { lamarg = fixarg; lambody = fixbody } in
      value_type_check ctx v #: fixname.ty tau
  | _, _ -> _typing_error __FILE__ __LINE__ "unimp"

and handle_ghost (ctx : Type_ctx.t) (tau : rty) : Type_ctx.t * rty =
  match tau with
  | ArrRty { arr_kind = GhostArr; rarg; retrty } -> (
      match rarg.rx with
      | None -> _failatwith __FILE__ __LINE__ "die"
      | Some x ->
          let ctx = Type_ctx.new_to_ctx ctx (x, rarg.rty) in
          handle_ghost ctx retrty)
  | _ -> (ctx, tau)

and value_type_syn (ctx : Type_ctx.t) (v : value typed) :
    (Type_ctx.t * rty) typing_result =
  let () = print_value_type_syn ctx v in
  match v.x with
  | VVar x -> (
      match Type_ctx.find_opt ctx x with
      | Some tau ->
          if is_arr tau then
            let tau = fresh_local_name tau in
            let ctx, tau = handle_ghost ctx tau in
            TypeSuccess (ctx, tau)
          else
            let tau = mk_eq_from_var x #: v.ty in
            TypeSuccess (ctx, tau)
      | None -> _typing_error __FILE__ __LINE__ "connot infer var")
  | VConst _ -> TypeSuccess (ctx, builtin_typing v.x)
  | _ -> _typing_error __FILE__ __LINE__ "unimp"

and values_type_check (ctx : Type_ctx.t) (vs : value typed list) (tau : rty) :
    (Type_ctx.t * rty) typing_result =
  match (vs, tau) with
  | [], _ -> TypeSuccess (ctx, tau)
  | v :: vs, ArrRty { arr_kind = NormalArr; rarg; retrty } ->
      let* ctx, _ = value_type_check ctx v rarg.rty in
      let retrty =
        match rarg.rx with
        | None -> retrty
        | Some x -> rty_subst_value (x, v.x) retrty
      in
      values_type_check ctx vs retrty
  | _ :: _, _ -> _failatwith __FILE__ __LINE__ "die"

and term_type_check (ctx : Type_ctx.t) (e : comp typed) (tau : rty) :
    (Type_ctx.t * rty) typing_result =
  let () = print_term_type_check ctx e tau in
  match e.x with
  | CVal v -> value_type_check ctx v #: e.ty tau
  | CLetE { lhs; rhs; letbody } ->
      let* ctx, lhs_rty =
        match rhs.x with
        | CApp { appf; apparg } ->
            let* ctx, tau_func = value_type_syn ctx appf in
            values_type_check ctx [ apparg ] tau_func
        | CAppOp { op; appopargs } ->
            let tau_op = fresh_local_name @@ op_type_syn op in
            let ctx, tau_op = handle_ghost ctx tau_op in
            let _ =
              Printf.printf "After Op:";
              Type_ctx.pretty_print ctx;
              Printf.printf "\n"
            in
            values_type_check ctx appopargs tau_op
        | _ -> _typing_error __FILE__ __LINE__ "unimp"
      in
      let ctx = Type_ctx.new_to_ctx ctx (lhs.x, lhs_rty) in
      term_type_check ctx letbody tau
  | _ -> _typing_error __FILE__ __LINE__ "unimp"

let typecheck (opctx : ROpTypectx.t) (rctx : RTypectx.t) (e : comp typed)
    (tau : rty) =
  let _ = cur_opctx := opctx in
  let ctx = Type_ctx.from_rctx rctx in
  let res = term_type_check ctx e tau in
  let () = Printf.printf "%s\n" @@ layout_typing_result res in
  ()
