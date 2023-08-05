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
    | OverRty of cty
    | ReachRty of lit Nt.typed
    | ArrRty of {
        arr_kind : arr_kind;
        rarg : string option utyped;
        retrty : rty;
      }

  and uty = UnderUty of cty | ReachUty of lit Nt.typed | ArrUty of rty
  [@@deriving sexp]

  and 'a utyped = { ux : 'a; uty : uty } [@@deriving sexp]

  type 'a rtyped = { rx : 'a; rty : rty }

  open Sugar

  let str_eq_to_bv y x =
    match x with Some x -> String.equal x y | None -> false

  let over_to_under = function
    | OverRty cty -> UnderUty cty
    | ReachRty lit -> ReachUty lit
    | ArrRty _ as t -> ArrUty t

  let uty_to_cty = function
    | UnderUty cty -> cty
    | ReachUty lit -> Nt.(mk_eq_lit v_name #: lit.ty lit.x)
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let uty_to_cty t = t |> over_to_under |> uty_to_cty
  let compare_uty l1 l2 = Sexplib.Sexp.compare (sexp_of_uty l1) (sexp_of_uty l2)
  let eq_uty l1 l2 = 0 == compare_pty l1 l2
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
      | BasePty { cty } -> BasePty { cty = subst_cty (y, z) cty }
      | TuplePty ptys -> TuplePty (List.map aux ptys)
      | ArrPty { arr_kind; rarg; retrty } ->
          let rarg = rarg.px #:: (aux rarg.pty) in
          if str_eq_to_bv y rarg.px then ArrPty { arr_kind; rarg; retrty }
          else ArrPty { arr_kind; rarg; retrty = subst (y, z) retrty }
    in
    aux rty

  and subst_uty (y, z) uty =
    match uty with
    | UnderUty cty -> UnderUty (C.subst (y, z) cty)
    | ReachUty lit ->
        if String.equal y v_name then uty
        else ReachUty Nt.(L.subst (y, z) #-> lit)
    | ArrRty rty -> ArrRty (subst_rty (y, z) rty)

  let subst_rty = subst

  let subst_id (y, z) rty =
    let z = AVar z in
    subst (y, z) rty

  let subst_regex_id (y, z) rty =
    let z = AVar z in
    subst_regex (y, z) rty

  (* fv *)

  let rec fv_pty rty =
    let rec aux rty =
      match rty with
      | BasePty { cty; _ } -> fv_cty cty
      | TuplePty ptys -> List.concat_map aux ptys
      | ArrPty { rarg; retrty; _ } ->
          let argfv = aux rarg.pty in
          let retfv =
            List.filter (fun x -> not (str_eq_to_bv x rarg.px)) @@ fv retrty
          in
          argfv @ retfv
    in
    aux rty

  and fv_sevent sevent =
    match sevent with
    | GuardEvent phi -> fv_prop phi
    | RetEvent pty -> fv_pty pty
    | EffEvent { vs; phi; v; _ } ->
        List.filter (fun y ->
            not (List.exists (fun x -> String.equal x.Nt.x y) (v :: vs)))
        @@ fv_prop phi

  and fv_regex regex =
    let rec aux regex =
      match regex with
      | EmptyA -> []
      | AnyA -> []
      | EpsilonA -> []
      | EventA se -> fv_sevent se
      | LorA (t1, t2) -> aux t1 @ aux t2
      | SetMinusA (t1, t2) -> aux t1 @ aux t2
      | LandA (t1, t2) -> aux t1 @ aux t2
      | SeqA (t1, t2) -> aux t1 @ aux t2
      | StarA t -> aux t
      | ComplementA t -> aux t
    in
    aux regex

  and fv = function
    | Pty pty -> fv_pty pty
    | Regty { prereg; postreg; _ } -> fv_regex prereg @ fv_regex postreg

  (* erase *)

  let rec erase_pty rty =
    let open Nt in
    let rec aux rty =
      match rty with
      | BasePty { cty; _ } -> erase_cty cty
      | TuplePty ptys -> Ty_tuple (List.map aux ptys)
      | ArrPty { rarg; retrty; arr_kind = PiArr } ->
          mk_arr (aux rarg.pty) (erase retrty)
      | ArrPty { retrty; arr_kind = SigamArr; _ } -> erase retrty
    in
    aux rty

  and erase = function Pty pty -> erase_pty pty | Regty { nty; _ } -> nty

  let ptyped_opt_erase { px; pty } =
    match px with None -> None | Some x -> Some Nt.{ x; ty = erase_pty pty }

  let ptyped_erase { px; pty } = Nt.{ x = px; ty = erase_pty pty }

  let pty_to_ret_rty pty =
    Regty
      {
        nty = erase_pty pty;
        prereg = StarA AnyA;
        postreg = EventA (RetEvent pty);
      }

  let regex_to_pty regex =
    match regex with
    | EventA (RetEvent pty) -> pty
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let pty_to_regex pty = EventA (RetEvent pty)

  let pty_to_cty pty =
    match pty with
    | BasePty { cty } -> cty
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let rtyped_force_to_ptyped file line { rx; rty } =
    match rty with
    | Pty pty -> { px = rx; pty }
    | _ -> _failatwith file line "die"

  (* gather lits/rtys *)

  open Zzdatatype.Datatype

  type gathered_lits = {
    global_lits : lit list;
    global_pty : pty list;
    local_lits : (string Nt.typed list * lit list) StrMap.t;
  }

  let gathered_lits_init () =
    { global_lits = []; global_pty = []; local_lits = StrMap.empty }

  let gathered_rm_dup { global_lits; global_pty; local_lits } =
    let global_lits = List.slow_rm_dup eq_lit global_lits in
    let global_pty = List.slow_rm_dup eq_pty global_pty in
    let local_lits =
      StrMap.map
        (fun (vs, lits) -> (vs, List.slow_rm_dup eq_lit lits))
        local_lits
    in
    { global_lits; global_pty; local_lits }

  let gather_from_sevent { global_lits; global_pty; local_lits } sevent =
    match sevent with
    | GuardEvent phi ->
        { global_lits = P.get_lits phi @ global_lits; global_pty; local_lits }
    | RetEvent pty ->
        { global_lits; global_pty = pty :: global_pty; local_lits }
    | EffEvent { op; phi; vs; v } ->
        let lits = P.get_lits phi in
        let vs' = List.map (fun x -> x.Nt.x) (v :: vs) in
        let is_contain_local_free lit =
          match List.interset ( == ) vs' @@ P.fv_lit lit with
          | [] -> false
          | _ -> true
        in
        let llits, glits = List.partition is_contain_local_free lits in
        let local_lits =
          StrMap.update op
            (fun l ->
              match l with
              | None -> Some (v :: vs, llits)
              | Some (_, l) -> Some (v :: vs, l @ llits))
            local_lits
        in
        let global_lits = global_lits @ glits in
        { global_lits; global_pty; local_lits }

  let gather_from_regex regex =
    let rec aux regex m =
      match regex with
      | EmptyA -> m
      | AnyA -> m
      | EpsilonA -> m
      | EventA se -> gather_from_sevent m se
      | LorA (t1, t2) -> aux t1 @@ aux t2 m
      | SetMinusA (t1, t2) -> aux t1 @@ aux t2 m
      | LandA (t1, t2) -> aux t1 @@ aux t2 m
      | SeqA (t1, t2) -> aux t1 @@ aux t2 m
      | StarA t -> aux t m
      | ComplementA t -> aux t m
    in
    aux regex (gathered_lits_init ())

  (* normalize name *)

  let rec normalize_name_pty tau1 =
    match tau1 with
    | BasePty { cty } -> BasePty { cty = normalize_name_cty cty }
    | TuplePty tys -> TuplePty (List.map normalize_name_pty tys)
    | ArrPty { arr_kind; rarg; retrty } ->
        let rarg = rarg.px #:: (normalize_name_pty rarg.pty) in
        let retrty = normalize_name_rty retrty in
        ArrPty { arr_kind; rarg; retrty }

  and normalize_name_sevent = function
    | GuardEvent phi -> GuardEvent phi
    | RetEvent pty -> RetEvent (normalize_name_pty pty)
    | EffEvent { op; vs; v; phi } ->
        let vs' = vs_names (List.length vs) in
        let tmp =
          _safe_combine __FILE__ __LINE__ (v :: vs) (v_ret_name :: vs')
        in
        let phi =
          List.fold_left
            (fun phi (x', x) -> P.subst_prop_id (x'.Nt.x, x) phi)
            phi tmp
        in
        let vs, v =
          match List.map (fun (v, x) -> Nt.{ x; ty = v.ty }) tmp with
          | [] -> _failatwith __FILE__ __LINE__ "die"
          | v :: vs -> (vs, v)
        in
        EffEvent { op; vs; v; phi }

  and noralize_name_regex regex =
    let rec aux regex =
      match regex with
      | AnyA | EmptyA | EpsilonA -> regex
      | EventA se -> EventA (normalize_name_sevent se)
      | LorA (t1, t2) -> LorA (aux t1, aux t2)
      | SetMinusA (t1, t2) -> SetMinusA (aux t1, aux t2)
      | LandA (t1, t2) -> LandA (aux t1, aux t2)
      | SeqA (t1, t2) -> SeqA (aux t1, aux t2)
      | StarA t -> StarA (aux t)
      | ComplementA t -> ComplementA (aux t)
    in
    aux regex

  and normalize_name_rty tau =
    match tau with
    | Pty tau -> Pty (normalize_name_pty tau)
    | Regty { nty; prereg; postreg } ->
        Regty
          {
            nty;
            prereg = noralize_name_regex prereg;
            postreg = noralize_name_regex postreg;
          }

  (* unify name *)

  let rec unify_name_pty (tau1, tau2) =
    match (tau1, tau2) with
    | BasePty _, BasePty _ -> (tau1, tau2)
    | TuplePty tys1, TuplePty tys2 ->
        let tys1, tys2 =
          List.split @@ List.map unify_name_pty
          @@ _safe_combine __FILE__ __LINE__ tys1 tys2
        in
        (TuplePty tys1, TuplePty tys2)
    | ( ArrPty { arr_kind = k1; rarg = rarg1; retrty = retrty1 },
        ArrPty { arr_kind = k2; rarg = rarg2; retrty = retrty2 } )
      when arr_eq k1 k2 ->
        let pty1, pty2 = unify_name_pty (rarg1.pty, rarg2.pty) in
        let (rarg1, rarg2), retrty2 =
          match (rarg1.px, rarg2.px) with
          | None, None -> ((None #:: pty1, None #:: pty2), retrty2)
          | Some x1, Some x2 ->
              ( ((Some x1) #:: pty1, (Some x1) #:: pty2),
                subst_id (x2, x1) retrty2 )
          | _, _ -> _failatwith __FILE__ __LINE__ "?"
        in
        let retrty1, retrty2 = unify_name_rty (retrty1, retrty2) in
        ( ArrPty { arr_kind = k1; rarg = rarg1; retrty = retrty1 },
          ArrPty { arr_kind = k2; rarg = rarg2; retrty = retrty2 } )
    | _, _ -> _failatwith __FILE__ __LINE__ "?"

  and unify_name_rty (tau1, tau2) =
    match (tau1, tau2) with
    | Pty tau1, Pty tau2 ->
        let tau1, tau2 = unify_name_pty (tau1, tau2) in
        (Pty tau1, Pty tau2)
    | Regty _, Regty _ -> (tau1, tau2)
    | Pty tau1, Regty _ -> unify_name_rty (pty_to_ret_rty tau1, tau2)
    | Regty _, Pty tau2 -> unify_name_rty (tau1, pty_to_ret_rty tau2)
  (* | _, _ -> _failatwith __FILE__ __LINE__ "?" *)

  let mk_unit_pty_from_prop phi = BasePty { cty = mk_unit_cty_from_prop phi }
  let mk_unit_rty_from_prop phi = Pty (mk_unit_pty_from_prop phi)
  let default_ty = mk_unit_rty_from_prop mk_true
  let xmap f { x; ty } = { x = f x; ty }
  let is_base_pty = function BasePty _ -> true | _ -> false

  (* regular expression *)

  let delimited_reverse regex =
    let rec aux regex =
      match regex with
      | AnyA | EmptyA | EpsilonA | EventA _ -> regex
      | LorA (t1, t2) -> LorA (aux t1, aux t2)
      | SetMinusA (t1, t2) -> SetMinusA (aux t1, aux t2)
      | LandA (t1, t2) -> LandA (aux t1, aux t2)
      | SeqA (t1, t2) -> SeqA (aux t2, aux t1)
      | StarA t -> StarA (aux t)
      | ComplementA t -> ComplementA (aux t)
    in
    aux regex

  (* stat *)

  let rec stat_num_events_am regex =
    let rec aux regex =
      match regex with
      | AnyA | EmptyA | EpsilonA -> 1
      | EventA se -> stat_num_events_sevent se
      | LorA (t1, t2) -> aux t1 + aux t2
      | SetMinusA (t1, t2) -> aux t1 + aux t2
      | LandA (t1, t2) -> aux t1 + aux t2
      | SeqA (t1, t2) -> aux t1 + aux t2
      | StarA t -> 1 + aux t
      | ComplementA t -> 1 + aux t
    in
    aux regex

  and stat_num_events_sevent se =
    match se with
    | GuardEvent _ -> 1
    | RetEvent pty -> stat_num_events_pty pty
    | EffEvent _ -> 1

  and stat_num_events_rty rty =
    match rty with
    | Pty pty -> stat_num_events_pty pty
    | Regty { prereg; postreg; _ } ->
        stat_num_events_am prereg + stat_num_events_am postreg

  and stat_num_events_pty rty =
    match rty with
    | BasePty _ -> 1
    | TuplePty _ -> 1
    | ArrPty { retrty; _ } -> stat_num_events_rty retrty

  let rec stat_lits_from_pty rty =
    let res =
      match rty with
      | BasePty { cty = { phi; _ }; _ } -> P.get_lits phi
      | TuplePty _ -> _failatwith __FILE__ __LINE__ "die"
      | ArrPty { rarg; retrty; _ } ->
          let l1 = stat_lits_from_pty rarg.pty in
          let l2 = stat_lits_from_rty retrty in
          l1 @ l2
    in
    res
  (* List.slow_rm_dup eq_lit @@ res *)

  and stat_lits_from_rty rty =
    let res =
      match rty with
      | Pty pty -> stat_lits_from_pty pty
      | Regty { prereg; postreg; _ } ->
          stat_lits_from_regex prereg @ stat_lits_from_regex postreg
    in
    res
  (* List.slow_rm_dup eq_lit @@ res *)

  and stat_lits_from_regex regex =
    let rec aux regex =
      match regex with
      | EmptyA -> []
      | AnyA -> []
      | EpsilonA -> []
      | EventA se -> stat_lits_from_sevent se
      | LorA (t1, t2) -> aux t1 @ aux t2
      | SetMinusA (t1, t2) -> aux t1 @ aux t2
      | LandA (t1, t2) -> aux t1 @ aux t2
      | SeqA (t1, t2) -> aux t1 @ aux t2
      | StarA t -> aux t
      | ComplementA t -> aux t
    in
    aux regex
  (* List.slow_rm_dup eq_lit (aux regex) *)

  and stat_lits_from_sevent sevent =
    let res =
      match sevent with
      | GuardEvent phi -> P.get_lits phi
      | RetEvent pty -> stat_lits_from_pty pty
      | EffEvent { phi; _ } -> P.get_lits phi
    in
    res
  (* List.slow_rm_dup eq_lit @@ res *)

  let stat_lits_from_rty_no_dup rty =
    List.slow_rm_dup eq_lit @@ stat_lits_from_rty rty

  (* mk bot/top *)

  let rec mk_bot_pty t =
    match t with
    | Nt.Ty_arrow (t1, t2) ->
        let px =
          match t1 with
          | Nt.Ty_arrow (_, _) -> None
          | _ -> Some (Rename.unique "x")
        in
        let pty = mk_top_pty t1 in
        let retrty = Pty (mk_bot_pty t2) in
        ArrPty { arr_kind = PiArr; rarg = { px; pty }; retrty }
    | Nt.Ty_tuple tys -> TuplePty (List.map mk_bot_pty tys)
    | _ -> BasePty { cty = mk_bot_cty t }

  and mk_top_pty t =
    match t with
    | Nt.Ty_arrow (t1, t2) ->
        let px =
          match t1 with
          | Nt.Ty_arrow (_, _) -> None
          | _ -> Some (Rename.unique "x")
        in
        let pty = mk_bot_pty t1 in
        let retrty = Pty (mk_top_pty t2) in
        ArrPty { arr_kind = PiArr; rarg = { px; pty }; retrty }
    | Nt.Ty_tuple tys -> TuplePty (List.map mk_top_pty tys)
    | _ -> BasePty { cty = mk_top_cty t }

  let is_arr_pty = function
    | ArrPty { arr_kind = PiArr; _ } -> true
    | _ -> false

  (* dummy interfaces *)
  let is_basic_tp _ = _failatwith __FILE__ __LINE__ "never happen"
  let is_dt _ = _failatwith __FILE__ __LINE__ "never happen"
  let destruct_arr_tp _ = _failatwith __FILE__ __LINE__ "unimp"
  let construct_arr_tp _ = _failatwith __FILE__ __LINE__ "unimp"
  let _type_unify _ _ = _failatwith __FILE__ __LINE__ "unimp"
  let to_smttyped _ = _failatwith __FILE__ __LINE__ "unimp"
  let typed_of_sexp _ = _failatwith __FILE__ __LINE__ "unimp"
  let sexp_of_typed _ = _failatwith __FILE__ __LINE__ "unimp"
  let _type_unify_ _ = _failatwith __FILE__ __LINE__ "unimp"

  let destruct_arr_one rty =
    match rty with
    | ArrPty { arr_kind = PiArr; rarg; retrty } -> (rarg, retrty)
    | _ -> _failatwith __FILE__ __LINE__ ""

  let get_argty rty =
    match rty with
    | Pty rty ->
        let rarg, _ = destruct_arr_one rty in
        Pty rarg.pty
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let get_retty rty =
    match rty with
    | Pty rty ->
        let _, retrty = destruct_arr_one rty in
        retrty
    | _ -> _failatwith __FILE__ __LINE__ "die"

  let snd_ty _ = _failatwith __FILE__ __LINE__ "unimp"
  let fst_ty _ = _failatwith __FILE__ __LINE__ "unimp"
  let bool_ty = default_ty
  let mk_tuple _ = _failatwith __FILE__ __LINE__ "unimp"
  let mk_arr _ = _failatwith __FILE__ __LINE__ "unimp"
  let int_ty = default_ty
  let unit_pty = BasePty { cty = mk_unit_cty_from_prop mk_true }
  let unit_ty = Pty unit_pty
  let to_smtty _ = _failatwith __FILE__ __LINE__ "unimp"
  let sexp_of_t _ = _failatwith __FILE__ __LINE__ "unimp"
  let t_of_sexp _ = _failatwith __FILE__ __LINE__ "unimp"
end
