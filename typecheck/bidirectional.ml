open Language
open TypedCore
open Rty
open Sugar
open Typeerr
open Typingaux
module Type_ctx = Type_ctx

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

let mk_over_constra_rty var retrty =
  let cty =
    match retrty with
    | BaseRty { cty; _ } -> cty
    | _ -> _failatwith __FILE__ __LINE__ "die"
  in
  let v, phi = to_v_prop cty in
  let phi = P.subst (v.x, value_to_lit var) phi in
  let rty = mk_unit_from_prop Under phi in
  (Rename.unique "_c", rty)

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
  | VVar _, _ ->
      let* ctx, syned_tau = value_type_syn ctx v in
      let _ = subtyping_check ctx (syned_tau, tau) in
      TypeSuccess (ctx, tau)
  | VLam { lamarg; lambody }, ArrRty { arr_kind = NormalArr; rarg; retrty } ->
      let ctx = Type_ctx.add_to_ctx ctx (lamarg.x, rarg.rty) in
      let retrty =
        match rarg.rx with
        | None -> retrty
        | Some x -> rty_subst_value (x, VVar lamarg.x) retrty
      in
      term_type_check ctx lambody retrty
  | VFix { fixname; fixarg; fixbody }, ArrRty { arr_kind = NormalArr; _ } ->
      let ctx = Type_ctx.add_to_ctx ctx (fixname.x, tau) in
      let v = VLam { lamarg = fixarg; lambody = fixbody } in
      value_type_check ctx v #: fixname.ty tau
  | _, _ -> _typing_error __FILE__ __LINE__ "unimp"

and handle_ghost (ctx : Type_ctx.t) (tau : rty) : Type_ctx.t * rty =
  match tau with
  | ArrRty { arr_kind = GhostArr; rarg; retrty } -> (
      match rarg.rx with
      | None -> _failatwith __FILE__ __LINE__ "die"
      | Some x ->
          let ctx = Type_ctx.add_to_ctx ctx (x, rarg.rty) in
          handle_ghost ctx retrty)
  | _ -> (ctx, tau)

and value_type_syn (ctx : Type_ctx.t) (v : value typed) :
    (Type_ctx.t * rty) typing_result =
  let () = print_value_type_syn ctx v in
  let res =
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
  in
  let () =
    match res with
    | TypeSuccess (_, rty) ->
        Printf.printf "Synthesized result: %s\n\n" (layout_rty rty)
    | TypeFailure (file, line, err_msg) ->
        Printf.printf "Type error at [%s]%i: %s\n\n" file line err_msg
  in
  res

and application_type_check (ctx : Type_ctx.t) (vs : value typed list)
    (tau : rty) : (Type_ctx.t * rty) typing_result =
  let rec aux ctx vs tau =
    match (vs, tau) with
    | [], _ -> TypeSuccess (ctx, tau)
    | v :: vs, ArrRty { arr_kind = NormalArr; rarg; retrty } ->
        let* ctx, _ = value_type_check ctx v rarg.rty in
        let ctx =
          match rarg.rty with
          | BaseRty _ ->
              Type_ctx.add_to_ctx ctx (mk_over_constra_rty v.x rarg.rty)
          (* | BaseRty { ou = Under; cty } -> ( *)
          (*     match v.x with *)
          (*     | VVar x -> Type_ctx.update_under_typing ctx (x, cty) *)
          (*     | _ -> ctx (\* Type_ctx.new_eqprop_to_ctx ctx (tlit, v) *\)) *)
          (* | BaseRty { ou = Under; _ } -> _failatwith __FILE__ __LINE__ "die" *)
          | _ -> ctx
        in
        let retrty =
          match rarg.rx with
          | None -> retrty
          | Some x -> rty_subst_value (x, v.x) retrty
        in
        aux ctx vs retrty
    | _ :: _, _ -> _failatwith __FILE__ __LINE__ "die"
  in
  let tau = overlize tau in
  let ctx, tau = handle_ghost ctx tau in
  aux ctx vs tau

and term_type_syn (ctx : Type_ctx.t) (e : comp typed) :
    (Type_ctx.t * rty) typing_result =
  let () = print_term_type_syn ctx e in
  match e.x with
  | CVal v -> value_type_syn ctx v #: e.ty
  | CLetE { lhs; rhs; letbody } ->
      let* ctx, lhs_rty =
        match rhs.x with
        | CApp { appf; apparg } ->
            let* ctx, tau_func = value_type_syn ctx appf in
            application_type_check ctx [ apparg ] tau_func
        | CAppOp { op; appopargs } ->
            let tau_op = fresh_local_name @@ op_type_syn op in
            (* let _ = *)
            (*   Printf.printf "After Op:"; *)
            (*   Type_ctx.pretty_print ctx; *)
            (*   Printf.printf "\n" *)
            (* in *)
            application_type_check ctx appopargs tau_op
        | _ -> _typing_error __FILE__ __LINE__ "unimp"
      in
      let ctx = Type_ctx.add_to_ctx ctx (lhs.x, lhs_rty) in
      let* ctx, tau = term_type_syn ctx letbody in
      let ctx, tau = Type_ctx.close_ctx_by_name (ctx, tau) lhs.x in
      TypeSuccess (ctx, tau)
  | CMatch { matched; match_cases } ->
      let ctx_and_taus =
        List.map
          (fun { constructor; args; exp } ->
            let dt_tau = dt_type_syn constructor in
            let ctx, dt_tau = handle_ghost ctx dt_tau in
            let argsrty, retrty = destruct_arr_rty dt_tau in
            (* let ctx = Type_ctx.add_to_ctx ctx constra in *)
            (* let ctx = *)
            (*   match matched.x with *)
            (*   | VVar x -> Type_ctx.update_under_typing ctx (x, ret_cty) *)
            (*   | _ -> ctx *)
            (* in *)
            let bindings =
              mk_over_constra_rty matched.x retrty
              :: (List.map (fun (arg, rarg) ->
                      match rarg.rx with
                      | None -> (arg.x, rarg.rty)
                      | Some _ -> _failatwith __FILE__ __LINE__ "die")
                 @@ _safe_combine __FILE__ __LINE__ args argsrty)
            in
            let ctx = List.fold_left Type_ctx.add_to_ctx ctx bindings in
            let* ctx, tau = term_type_syn ctx exp in
            let ctx, tau =
              List.fold_right
                (fun (x, _) (ctx, tau) ->
                  Type_ctx.close_ctx_by_name (ctx, tau) x)
                bindings (ctx, tau)
            in
            TypeSuccess (ctx, tau))
          match_cases
      in
      let ctx_and_taus =
        List.filter_map
          (fun r ->
            match r with TypeSuccess x -> Some x | TypeFailure _ -> None)
          ctx_and_taus
      in
      let ctx, tau = merge_ctx_and_types ctx_and_taus in
      TypeSuccess (ctx, tau)
  | _ -> _failatwith __FILE__ __LINE__ "die"

and merge_ctx_and_types ctx_and_taus =
  let () = Printf.printf "merge_ctx_and_types:\n" in
  let () =
    List.iteri
      (fun i (ctx, tau) ->
        Printf.printf "#%i\n" i;
        Type_ctx.pretty_print ctx;
        Printf.printf "  ~~  %s\n" (layout_rty tau))
      ctx_and_taus
  in
  let ctxs, taus = List.split ctx_and_taus in
  let ctx = Type_ctx.merge_ctxs ctxs in
  let tau = Rty.munion taus in
  (ctx, tau)

and term_type_check (ctx : Type_ctx.t) (e : comp typed) (tau : rty) :
    (Type_ctx.t * rty) typing_result =
  let () = print_term_type_check ctx e tau in
  match e.x with
  | CVal v -> value_type_check ctx v #: e.ty tau
  | CLetE { lhs; rhs; letbody } ->
      let* ctx', lhs_rty =
        match rhs.x with
        | CApp { appf; apparg } ->
            let* ctx, tau_func = value_type_syn ctx appf in
            application_type_check ctx [ apparg ] tau_func
        | CAppOp { op; appopargs } ->
            let tau_op = fresh_local_name @@ op_type_syn op in
            (* let _ = *)
            (*   Printf.printf "After Op:"; *)
            (*   Type_ctx.pretty_print ctx; *)
            (*   Printf.printf "\n" *)
            (* in *)
            application_type_check ctx appopargs tau_op
        | _ -> _typing_error __FILE__ __LINE__ "unimp"
      in
      let ctx' = Type_ctx.add_to_ctx ctx' (lhs.x, lhs_rty) in
      let* ctx', tau = term_type_check ctx' letbody tau in
      let ctx, tau = Type_ctx.close_ctx_by_diff ctx (ctx', tau) in
      TypeSuccess (ctx, tau)
  | CMatch _ ->
      let* ctx, tau' = term_type_syn ctx e in
      if subtyping_check tau' tau then TypeSuccess (ctx, tau)
      else _typing_error __FILE__ __LINE__ "match"
  | _ -> _typing_error __FILE__ __LINE__ "unimp"

let typecheck (opctx : ROpTypectx.t) (rctx : RTypectx.t) (e : comp typed)
    (tau : rty) =
  let _ = cur_opctx := opctx in
  let ctx = Type_ctx.from_rctx rctx in
  let res = term_type_check ctx e tau in
  let () = Printf.printf "%s\n" @@ layout_typing_result res in
  ()
