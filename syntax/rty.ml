open Langlike

module F (L : Lit.T) = struct
  open Sexplib.Std
  module C = Cty.F (L)
  include C

  type rty =
    | SingleRty of lit Nt.typed  (** singlton type *)
    | BaseRty of { cty : cty }  (** overlap type *)
    | ArrRty of {
        arr_kind : arr_kind;
        rarg : string option rtyped;
        retrty : rty;
      }  (** function type / ghost function type *)

  and 'a rtyped = { rx : 'a; rty : rty } [@@deriving sexp]

  let ( #:: ) rx rty = { rx; rty }
  let ( #--> ) f { rx; rty } = { rx = f rx; rty }

  open Sugar

  (* erase *)

  let rec erase_rty = function
    | SingleRty tlit -> tlit.Nt.ty
    | BaseRty { cty } -> erase cty
    | ArrRty { rarg; retrty; arr_kind } -> (
        let retrty' = erase_rty retrty in
        match arr_kind with
        | NormalArr -> Nt.mk_arr (erase_rty rarg.rty) retrty'
        | GhostArr -> retrty')

  let erase_rtyped { rx; rty } = Nt.{ x = rx; ty = erase_rty rty }

  let erase_rtyped_opt { rx; rty } =
    match rx with None -> None | Some x -> Some Nt.{ x; ty = erase_rty rty }

  (* well-formed *)

  let rec destruct_normal_arr_rtyopt rty =
    match rty with
    | BaseRty _ | SingleRty _ -> Some ([], rty)
    | ArrRty { arr_kind = NormalArr; rarg; retrty } ->
        let* parartys, retrty = destruct_normal_arr_rtyopt retrty in
        Some (rarg :: parartys, retrty)
    | ArrRty { arr_kind = GhostArr; _ } -> None

  let rec destruct_arr_rtyopt rty =
    match rty with
    | BaseRty _ | SingleRty _ -> Some ([], [], rty)
    | ArrRty { arr_kind = NormalArr; _ } ->
        let* parartys, retrty = destruct_normal_arr_rtyopt rty in
        Some ([], parartys, retrty)
    | ArrRty { arr_kind = GhostArr; rarg; retrty } -> (
        let* gparartys, parartys, retrty = destruct_arr_rtyopt retrty in
        match (rarg.rx, rarg.rty) with
        | Some x, BaseRty { cty } ->
            Some ((x, cty) :: gparartys, parartys, retrty)
        | _, _ -> _failatwith __FILE__ __LINE__ "die")

  let destruct_arr_rty rty =
    match destruct_arr_rtyopt rty with
    | Some (a, b, c) -> (a, b, c)
    | None -> _failatwith __FILE__ __LINE__ "die"

  let reconstruct_rty (gparas, paras, retty) =
    let res =
      List.fold_right
        (fun rarg retrty -> ArrRty { arr_kind = NormalArr; rarg; retrty })
        paras retty
    in
    let res =
      List.fold_right
        (fun (x, cty) retrty ->
          ArrRty
            {
              arr_kind = GhostArr;
              rarg = { rx = Some x; rty = BaseRty { cty } };
              retrty;
            })
        gparas res
    in
    res

  let is_valid rty =
    match destruct_arr_rtyopt rty with Some _ -> true | None -> false

  let is_inc_base = function BaseRty _ | SingleRty _ -> true | _ -> false
  let is_over_base = is_inc_base

  let is_under_base rty =
    match destruct_arr_rtyopt rty with
    | Some (_ :: _, [], c) -> is_inc_base c
    | _ -> false

  let is_base rty = is_valid rty && (Nt.is_basic_tp @@ erase_rty rty)
  let is_arr rty = is_valid rty && not (Nt.is_basic_tp @@ erase_rty rty)

  (* let rty_to_cty = function *)
  (*   | BaseRty { cty; _ } -> cty *)
  (*   | _ -> _failatwith __FILE__ __LINE__ "die" *)

  let compare_rty t1 t2 = Sexplib.Sexp.compare (sexp_of_rty t1) (sexp_of_rty t2)
  let eq_rty tau1 tau2 = 0 == compare_rty tau1 tau2
  let mk_unit_from_prop phi = BaseRty { cty = C.mk_unit_from_prop phi }
  let mk_eq_from_var x = SingleRty Nt.((C.AVar x.x) #: x.ty)

  (* subst *)

  let rec subst (y, z) rty =
    let rec arx rty =
      match rty with
      | SingleRty tlit -> SingleRty Nt.((L.subst (y, z) tlit.x) #: tlit.ty)
      | BaseRty { cty } -> BaseRty { cty = C.subst (y, z) cty }
      | ArrRty { arr_kind; rarg; retrty } ->
          let rarg = rarg.rx #:: (subst (y, z) rarg.rty) in
          let retrty =
            match rarg.rx with
            | Some x when String.equal x y -> retrty
            | _ -> arx retrty
          in
          ArrRty { arr_kind; rarg; retrty }
    in
    arx rty

  (* fv *)

  let rec fv rty =
    match rty with
    | SingleRty tlit -> L.fv tlit.Nt.x
    | BaseRty { cty; _ } -> C.fv cty
    | ArrRty { rarg; retrty; _ } ->
        let argfv = fv rarg.rty in
        let retfv = fv retrty in
        let retfv =
          match rarg.rx with
          | None -> retfv
          | Some x -> Zzdatatype.Datatype.List.remove_elt String.equal x retfv
        in
        argfv @ retfv

  (* normalize name *)

  let rec normalize_name tau =
    match tau with
    | SingleRty _ -> tau
    | BaseRty { cty } -> (
        match C.to_tlit_opt cty with
        | None -> BaseRty { cty = C.normalize_name cty }
        | Some tlit -> SingleRty tlit)
    | ArrRty { arr_kind; rarg; retrty } ->
        let rarg = rarg.rx #:: (normalize_name rarg.rty) in
        let retrty = normalize_name retrty in
        ArrRty { arr_kind; rarg; retrty }

  (* fresh local name *)

  let rec fresh_local_name tau =
    match tau with
    | SingleRty _ | BaseRty _ -> tau
    | ArrRty { arr_kind; rarg; retrty } -> (
        let rarg_ty = fresh_local_name rarg.rty in
        match rarg.rx with
        | None ->
            let rarg = None #:: rarg_ty in
            ArrRty { arr_kind; rarg; retrty = fresh_local_name retrty }
        | Some x ->
            let fresh_name = Rename.unique x in
            let rarg = (Some fresh_name) #:: rarg_ty in
            let retrty = subst (x, L.AVar fresh_name) retrty in
            ArrRty { arr_kind; rarg; retrty = fresh_local_name retrty })

  (* (\* overlize function type *\) *)

  (* let overlize tau = *)
  (*   let rec aux ghost_param normal_param tau = *)
  (*     match (tau, normal_param) with *)
  (*     | BaseRty _, _ -> (ghost_param, normal_param, tau) *)
  (*     | ArrRty { arr_kind = GhostArr; rarg; retrty }, [] -> *)
  (*         aux (ghost_param @ [ rarg ]) [] retrty *)
  (*     | ArrRty { arr_kind = GhostArr; _ }, _ -> *)
  (*         _failatwith __FILE__ __LINE__ "die" *)
  (*     | ArrRty { arr_kind = NormalArr; rarg; retrty }, _ -> ( *)
  (*         match rarg.rty with *)
  (*         | BaseRty { refinement_kind = Under; cty } -> *)
  (*             let x = *)
  (*               match rarg.rx with *)
  (*               | None -> Rename.unique "_x" *)
  (*               | Some _ -> _failatwith __FILE__ __LINE__ "die" *)
  (*             in *)
  (*             let ghost = *)
  (*               (Some x) #:: (BaseRty { refinement_kind = Over; cty }) *)
  (*             in *)
  (*             let rarg = *)
  (*               None #:: Nt.(mk_eq_from_var x #: (erase_rty rarg.rty)) *)
  (*             in *)
  (*             aux (ghost_param @ [ ghost ]) (normal_param @ [ rarg ]) retrty *)
  (*         | _ -> aux ghost_param (normal_param @ [ rarg ]) retrty) *)
  (*   in *)
  (*   let ghost_param, normal_param, tau = aux [] [] tau in *)
  (*   let tau = *)
  (*     List.fold_right *)
  (*       (fun rarg retrty -> ArrRty { arr_kind = NormalArr; rarg; retrty }) *)
  (*       normal_param tau *)
  (*   in *)
  (*   let tau = *)
  (*     List.fold_right *)
  (*       (fun rarg retrty -> ArrRty { arr_kind = GhostArr; rarg; retrty }) *)
  (*       ghost_param tau *)
  (*   in *)
  (*   tau *)

  (* (\* unify name *\) *)

  (* let rec unify_name (tau1, tau2) = *)
  (*   match (tau1, tau2) with *)
  (*   | ( BaseRty { cty = cty1 }, *)
  (*       BaseRty { cty = cty2 } ) *)
  (*     when refinement_kind_eq refinement_kind refinement_kind' -> *)
  (*       (BaseRty { cty = cty1 }, BaseRty { cty = cty2 }) *)
  (*   | ( ArrRty { arr_kind; rarg = rarg1; retrty = retrty1 }, *)
  (*       ArrRty { arr_kind = arr_kind'; rarg = rarg2; retrty = retrty2 } ) *)
  (*     when arr_kind_eq arr_kind arr_kind' -> *)
  (*       let rty1, rty2 = unify_name (rarg1.rty, rarg2.rty) in *)
  (*       let rarg_rx, retrty2 = *)
  (*         match (rarg1.rx, rarg2.rx) with *)
  (*         | None, None -> (None, retrty2) *)
  (*         | Some x1, Some x2 -> (Some x1, subst (x2, AVar x1) retrty2) *)
  (*         | _, _ -> _failatwith __FILE__ __LINE__ "?" *)
  (*       in *)
  (*       let rarg1, rarg2 = (rarg_rx #:: rty1, rarg_rx #:: rty2) in *)
  (*       let retrty1, retrty2 = unify_name (retrty1, retrty2) in *)
  (*       ( ArrRty { arr_kind; rarg = rarg1; retrty = retrty1 }, *)
  (*         ArrRty { arr_kind; rarg = rarg2; retrty = retrty2 } ) *)
  (*   | _, _ -> _failatwith __FILE__ __LINE__ "?" *)

  (* union and intersect *)

  (* let union tau1 tau2 = *)
  (*   match (tau1, tau2) with *)
  (*   | ( BaseRty { refinement_kind = Under; cty = cty1 }, *)
  (*       BaseRty { refinement_kind = Under; cty = cty2 } ) -> *)
  (*       BaseRty { refinement_kind = Under; cty = C.union cty1 cty2 } *)
  (*   | _, _ -> _failatwith __FILE__ __LINE__ "die" *)

  (* let munion taus = *)
  (*   match taus with *)
  (*   | [] -> _failatwith __FILE__ __LINE__ "die" *)
  (*   | tau :: taus -> List.fold_left union tau taus *)

  (* mk bot/top *)
  (* TODO: what is a bot arr type? *)
  (* let mk_bot_rty t = *)
  (*   match t with *)
  (*   | Nt.Ty_tuple _ -> _failatwith __FILE__ __LINE__ "die" *)
  (*   | Nt.Ty_arrow _ -> _failatwith __FILE__ __LINE__ "die" *)
  (*   | _ -> BaseRty (C.mk_bot t) *)

  (* let mk_top_rty t = *)
  (*   match t with *)
  (*   | Nt.Ty_tuple _ -> _failatwith __FILE__ __LINE__ "die" *)
  (*   | Nt.Ty_arrow _ -> _failatwith __FILE__ __LINE__ "die" *)
  (*   | _ -> BaseRty (C.mk_top t) *)
end
