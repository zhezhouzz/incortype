open Langlike

module F (L : Lit.T) = struct
  open Sexplib.Std
  module C = Cty.F (L)
  include C

  type arr_kind = NormalArr | GhostArr [@@deriving sexp]
  type ou = Over | Under [@@deriving sexp]

  let ou_eq a b =
    match (a, b) with Over, Over | Under, Under -> true | _, _ -> false

  let arr_eq k1 k2 =
    match (k1, k2) with
    | NormalArr, NormalArr | GhostArr, GhostArr -> true
    | _, _ -> false

  type rty =
    | BaseRty of { ou : ou; cty : cty }
    | ArrRty of {
        arr_kind : arr_kind;
        rarg : string option rtyped;
        retrty : rty;
      }

  and 'a rtyped = { rx : 'a; rty : rty } [@@deriving sexp]

  let ( #:: ) rx rty = { rx; rty }
  let ( #--> ) f { rx; rty } = { rx = f rx; rty }

  open Sugar

  let is_over = function BaseRty { ou = Under; _ } -> false | _ -> true
  let is_under rty = not (is_over rty)
  let is_base = function BaseRty _ -> true | _ -> false
  let is_arr = function ArrRty _ -> true | _ -> false

  let over_to_under = function
    | BaseRty { ou = Over; cty } -> BaseRty { ou = Under; cty }
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let rty_to_cty = function
    | BaseRty { cty; _ } -> cty
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let compare_rty t1 t2 = Sexplib.Sexp.compare (sexp_of_rty t1) (sexp_of_rty t2)
  let eq_rty tau1 tau2 = 0 == compare_rty tau1 tau2

  (* subst *)

  let rec subst (y, z) rty =
    let rec arx rty =
      match rty with
      | BaseRty { ou; cty } -> BaseRty { ou; cty = C.subst (y, z) cty }
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

  (* erase *)

  let rec erase_rty = function
    | BaseRty { cty; _ } -> erase cty
    | ArrRty { rarg; retrty; arr_kind } -> (
        let retrty' = erase_rty retrty in
        match arr_kind with
        | NormalArr -> Nt.mk_arr (erase_rty rarg.rty) retrty'
        | GhostArr -> retrty')

  let erase_rtyped { rx; rty } = Nt.{ x = rx; ty = erase_rty rty }

  let erase_rtyped_opt { rx; rty } =
    match rx with None -> None | Some x -> Some Nt.{ x; ty = erase_rty rty }

  (* normalize name *)

  let rec normalize_name tau =
    match tau with
    | BaseRty { ou; cty } -> BaseRty { ou; cty = C.normalize_name cty }
    | ArrRty { arr_kind; rarg; retrty } ->
        let rarg = rarg.rx #:: (normalize_name rarg.rty) in
        let retrty = normalize_name retrty in
        ArrRty { arr_kind; rarg; retrty }

  (* unify name *)

  let rec unify_name (tau1, tau2) =
    match (tau1, tau2) with
    | BaseRty { ou; cty = cty1 }, BaseRty { ou = ou'; cty = cty2 }
      when ou_eq ou ou' ->
        (BaseRty { ou; cty = cty1 }, BaseRty { ou; cty = cty2 })
    | ( ArrRty { arr_kind; rarg = rarg1; retrty = retrty1 },
        ArrRty { arr_kind = arr_kind'; rarg = rarg2; retrty = retrty2 } )
      when arr_eq arr_kind arr_kind' ->
        let rty1, rty2 = unify_name (rarg1.rty, rarg2.rty) in
        let rarg_rx, retrty2 =
          match (rarg1.rx, rarg2.rx) with
          | None, None -> (None, retrty2)
          | Some x1, Some x2 -> (Some x1, subst (x2, AVar x1) retrty2)
          | _, _ -> _failatwith __FILE__ __LINE__ "?"
        in
        let rarg1, rarg2 = (rarg_rx #:: rty1, rarg_rx #:: rty2) in
        let retrty1, retrty2 = unify_name (retrty1, retrty2) in
        ( ArrRty { arr_kind; rarg = rarg1; retrty = retrty1 },
          ArrRty { arr_kind; rarg = rarg2; retrty = retrty2 } )
    | _, _ -> _failatwith __FILE__ __LINE__ "?"

  let mk_unit_from_prop ou phi = BaseRty { ou; cty = C.mk_unit_from_prop phi }

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
