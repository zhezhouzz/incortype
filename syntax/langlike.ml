include Normalty.Connective

module type Sexpable = sig
  type t

  val sexp_of_t : t -> Sexplib.Sexp.t
end

module SexpCompare =
functor
  (T : Sexpable)
  ->
  struct
    open T

    let compare a b = Sexplib.Sexp.compare (sexp_of_t a) (sexp_of_t b)
    let eq a b = compare a b == 0
  end

module type Layoutable = sig
  type t

  val layout : t -> string
end

module type BindingName = sig
  type t

  val equal : t -> t -> bool
  val layout : t -> string
end

module Nt = struct
  include Normalty.Ntyped

  let from_nt t = t
  let eq_ty t = mk_arr t (mk_arr t bool_ty)
end

module ONt = struct
  include Normalty.NOpttyped

  let from_nt t = Some t
  let eq_ty t = mk_arr t (mk_arr t bool_ty)
end

type arr_kind = NormalArr | GhostArr [@@deriving sexp]

let arr_kind_eq k1 k2 =
  match (k1, k2) with
  | NormalArr, NormalArr | GhostArr, GhostArr -> true
  | _, _ -> false

type refinement_kind = Over | Under | Overlap [@@deriving sexp]

let refinement_kind_eq a b =
  match (a, b) with
  | Over, Over | Under, Under | Overlap, Overlap -> true
  | _, _ -> false

type rty_kind = RtyLib | RtyToCheck

let v_name = "v"

open Sugar

let vs_names n = List.init n (fun i -> spf "%s%i" v_name i)

let vs_names_from_types tps =
  let open Nt in
  let n = List.length tps in
  let vs = vs_names n in
  List.map (fun (x, ty) -> x #: ty) @@ _safe_combine __FILE__ __LINE__ vs tps
