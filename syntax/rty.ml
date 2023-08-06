open Langlike

module F (L : Lit.T) = struct
  open Sexplib.Std
  module C = Cty.F (L)
  include C

  type arr_kind = NormalArr | GhostArr [@@deriving sexp]

  let arr_eq k1 k2 =
    match (k1, k2) with
    | NormalArr, NormalArr | GhostArr, GhostArr -> true
    | _, _ -> false

  type rty =
    | BaseRty of cty
    | ArrRty of {
        arr_kind : arr_kind;
        rarg : string option utyped;
        retrty : rty;
      }

  and uty = BaseUty of cty | ArrUty of rty [@@deriving sexp]
  and 'a utyped = { ux : 'a; uty : uty } [@@deriving sexp]

  type 'a rtyped = { rx : 'a; rty : rty }

  open Sugar

  let str_eq_to_bv y x =
    match x with Some x -> String.equal x y | None -> false

  let over_to_under = function
    | BaseRty cty -> BaseUty cty
    | ArrRty _ as t -> ArrUty t

  let uty_to_cty = function
    | BaseUty cty -> cty
    (* | ReachUty lit -> Nt.(mk_eq_lit v_name #: lit.ty lit.x) *)
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let uty_to_cty t = t |> over_to_under |> uty_to_cty
  let compare_uty l1 l2 = Sexplib.Sexp.compare (sexp_of_uty l1) (sexp_of_uty l2)
  let eq_uty l1 l2 = 0 == compare_uty l1 l2
  let compare_rty t1 t2 = Sexplib.Sexp.compare (sexp_of_rty t1) (sexp_of_rty t2)
  let eq_rty tau1 tau2 = 0 == compare_rty tau1 tau2
  let ( #:: ) rx rty = { rx; rty }
  let ( #--> ) f { rx; rty } = { rx = f rx; rty }
  let ( #::: ) ux uty = { ux; uty }
  let ( #---> ) f { ux; uty } = { ux = f ux; uty }

  (* subst *)

  let rec subst_rty (y, z) rty =
    let rec aux rty =
      match rty with
      | BaseRty cty -> BaseRty (C.subst (y, z) cty)
      | ArrRty { arr_kind; rarg; retrty } ->
          let rarg = rarg.ux #::: (subst_uty (y, z) rarg.uty) in
          let retrty =
            match rarg.ux with
            | Some x when String.equal x y -> retrty
            | _ -> aux retrty
          in
          ArrRty { arr_kind; rarg; retrty }
    in
    aux rty

  and subst_uty (y, z) uty =
    match uty with
    | BaseUty cty -> BaseUty (C.subst (y, z) cty)
    | ArrUty rty -> ArrUty (subst_rty (y, z) rty)

  (* fv *)

  (* open Zzdatatype.Datatype *)

  let rec fv_rty rty =
    match rty with
    | BaseRty cty -> C.fv cty
    | ArrRty { rarg; retrty; _ } ->
        let argfv = fv_uty rarg.uty in
        let retfv = fv_rty retrty in
        let retfv =
          match rarg.ux with
          | None -> retfv
          | Some x -> Zzdatatype.Datatype.List.remove_elt String.equal x retfv
        in
        argfv @ retfv

  and fv_uty = function BaseUty cty -> C.fv cty | ArrUty rty -> fv_rty rty

  (* erase *)

  let rec erase_uty = function
    | BaseUty cty -> C.erase cty
    | ArrUty rty -> erase_rty rty

  and erase_rty = function
    | BaseRty cty -> erase cty
    | ArrRty { rarg; retrty; arr_kind } -> (
        let retrty' = erase_rty retrty in
        match arr_kind with
        | NormalArr -> Nt.mk_arr (erase_uty rarg.uty) retrty'
        | GhostArr -> retrty')

  let erase_utyped { ux; uty } = Nt.{ x = ux; ty = erase_uty uty }

  let erase_utyped_opt { ux; uty } =
    match ux with None -> None | Some x -> Some Nt.{ x; ty = erase_uty uty }

  (* normalize name *)

  let rec normalize_name_rty tau =
    match tau with
    | BaseRty cty -> BaseRty (C.normalize_name cty)
    | ArrRty { arr_kind; rarg; retrty } ->
        let rarg = rarg.ux #::: (normalize_name_uty rarg.uty) in
        let retrty = normalize_name_rty retrty in
        ArrRty { arr_kind; rarg; retrty }

  and normalize_name_uty tau =
    match tau with
    | BaseUty cty -> BaseUty (C.normalize_name cty)
    | ArrUty rty -> ArrUty (normalize_name_rty rty)

  (* unify name *)

  let rec unify_name_rty (tau1, tau2) =
    match (tau1, tau2) with
    | BaseRty _, BaseRty _ -> (tau1, tau2)
    | ( ArrRty { arr_kind; rarg = rarg1; retrty = retrty1 },
        ArrRty { arr_kind = arr_kind'; rarg = rarg2; retrty = retrty2 } )
      when arr_eq arr_kind arr_kind' ->
        let uty1, uty2 = unify_name_uty (rarg1.uty, rarg2.uty) in
        let rarg_ux, retrty2 =
          match (rarg1.ux, rarg2.ux) with
          | None, None -> (None, retrty2)
          | Some x1, Some x2 -> (Some x1, subst_rty (x2, AVar x1) retrty2)
          | _, _ -> _failatwith __FILE__ __LINE__ "?"
        in
        let rarg1, rarg2 = (rarg_ux #::: uty1, rarg_ux #::: uty2) in
        let retrty1, retrty2 = unify_name_rty (retrty1, retrty2) in
        ( ArrRty { arr_kind; rarg = rarg1; retrty = retrty1 },
          ArrRty { arr_kind; rarg = rarg2; retrty = retrty2 } )
    | _, _ -> _failatwith __FILE__ __LINE__ "?"

  and unify_name_uty (tau1, tau2) =
    match (tau1, tau2) with
    | BaseUty _, BaseUty _ -> (tau1, tau2)
    | ArrUty rty1, ArrUty rty2 ->
        let rty1, rty2 = unify_name_rty (rty1, rty2) in
        (ArrUty rty1, ArrUty rty2)
    | _, _ -> _failatwith __FILE__ __LINE__ "?"

  let mk_unit_rty_from_prop phi = BaseRty (C.mk_unit_from_prop phi)
  let mk_unit_uty_from_prop phi = over_to_under @@ mk_unit_rty_from_prop phi
  let is_base_rty = function BaseRty _ -> true | _ -> false
  let is_base_uty = function BaseUty _ -> true | _ -> false

  (* mk bot/top *)
  (* TODO: what is a bot arr type? *)
  let mk_bot_rty t =
    match t with
    | Nt.Ty_tuple _ -> _failatwith __FILE__ __LINE__ "die"
    | Nt.Ty_arrow _ -> _failatwith __FILE__ __LINE__ "die"
    | _ -> BaseRty (C.mk_bot t)

  let mk_top_rty t =
    match t with
    | Nt.Ty_tuple _ -> _failatwith __FILE__ __LINE__ "die"
    | Nt.Ty_arrow _ -> _failatwith __FILE__ __LINE__ "die"
    | _ -> BaseRty (C.mk_top t)
end
