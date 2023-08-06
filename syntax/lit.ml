open Langlike

module type TT = sig
  include Typed.T

  val from_nt : Normalty.Ntyped.t -> t
end

module type T = sig
  include TT

  type lit =
    | AC of Constant.t
    | AVar of string
    | AEq of lit typed * lit typed
    | AAppOp of Op.t typed * lit typed list
  [@@deriving sexp]

  (* for parsing *)
  val mk_bool : bool -> lit
  val mk_eq : lit typed -> lit typed -> lit typed
  val mk_teq : Nt.t -> lit -> lit -> lit typed

  (* cast *)
  val to_id : lit -> string
  val tto_id : lit typed -> string typed
  val to_id_list : lit list -> string list
  val tto_id_list : lit typed list -> string typed list
  val to_bool_opt : lit -> bool option
  val id_to_lit : string -> lit

  (* susbt *)
  val subst : string * lit -> lit -> lit
  val tsubst : string * lit -> lit typed -> lit typed
  val msubst : (string * lit) list -> lit -> lit
  val mtsubst : (string * lit) list -> lit typed -> lit typed

  (* FV *)
  val fv : lit -> string list
  val tfv : lit typed -> string list
  val tsfv : lit typed list -> string list

  (* aux *)
  val get_eq_by_name : lit -> string -> lit option

  (* val mk_int_l1_eq_l2 : lit -> lit -> lit *)
  (* val find_assignment_of_intvar : lit -> string -> lit option *)
end

module F (Ty : TT) : T with type t = Ty.t and type 'a typed = 'a Ty.typed =
struct
  open Sexplib.Std
  module T = Ty
  include Ty

  type lit =
    | AC of Constant.t
    | AVar of string
    | AEq of lit typed * lit typed
    | AAppOp of Op.t typed * lit typed list
  [@@deriving sexp]

  open Sugar

  let id_to_lit x = AVar x
  let to_id = function AVar x -> x | _ -> _failatwith __FILE__ __LINE__ "die"
  let tto_id x = to_id #-> x
  let to_id_list l = List.map (fun x -> to_id x) l
  let tto_id_list l = List.map tto_id l
  let to_bool_opt = function AC (Constant.B b) -> Some b | _ -> None
  let mk_bool b = AC (Constant.B b)

  (* let get_var_opt = function AVar x -> Some x | _ -> None *)
  let mk_eq l1 l2 = (AEq (l1, l2)) #: T.bool_ty

  let mk_teq nt l1 l2 =
    let l1 = l1 #: (T.from_nt nt) in
    let l2 = l2 #: (T.from_nt nt) in
    (AEq (l1, l2)) #: (T.from_nt Nt.Ty_bool)

  let get_eq_args_opt = function AEq (t1, t2) -> Some (t1, t2) | _ -> None

  let get_eq_by_name lit x =
    let* l1, l2 = get_eq_args_opt lit in
    match (l1.x, l2.x) with
    | AVar x1, _ when String.equal x x1 -> Some l2.x
    | _, AVar x2 when String.equal x x2 -> Some l1.x
    | _, _ -> None

  (* let mk_eq_lit { x; ty } lit = *)
  (*   if T.eq unit_ty ty || not (T.is_basic_tp ty) then *)
  (*     _failatwith __FILE__ __LINE__ "die" *)
  (*   else *)
  (*     let eq_op = Op.mk_eq_op #: (eq_ty ty) in *)
  (*     AAppOp (eq_op, [ (AVar x) #: ty; lit #: ty ]) *)

  (* let mk_eq_lit { x; ty } lit = *)
  (*   if T.eq unit_ty ty || not (T.is_basic_tp ty) then *)
  (*     _failatwith __FILE__ __LINE__ "die" *)
  (*   else *)
  (*     let eq_op = Op.mk_eq_op #: (eq_ty ty) in *)
  (*     AAppOp (eq_op, [ (AVar x) #: ty; lit #: ty ]) *)

  (* let mk_int_l1_eq_l2 l1 l2 = *)
  (*   let eq_op = Op.mk_eq_op #: (eq_ty int_ty) in *)
  (*   AAppOp (eq_op, [ l1 #: int_ty; l2 #: int_ty ]) *)

  (* let get_subst_pair a b = *)
  (*   match get_var_opt a with Some a -> [ (a, b) ] | None -> [] *)

  (* let get_eqlits lit = *)
  (*   match lit with *)
  (*   | AAppOp (op, [ a; b ]) when Op.id_eq_op op.x -> *)
  (*       get_subst_pair a.x b.x @ get_subst_pair b.x a.x *)
  (*   | _ -> [] *)

  (* let find_assignment_of_intvar lit x = *)
  (*   match lit with *)
  (*   | AAppOp (op, [ a; b ]) when Op.id_eq_op op.x -> ( *)
  (*       match (a.x, b.x) with *)
  (*       | AVar y, _ when String.equal x y -> Some b.x *)
  (*       | _, AVar y when String.equal x y -> Some a.x *)
  (*       | _, _ -> None) *)
  (*   | _ -> None *)

  (* open Sugar *)

  (* let get_eqlit_by_name lit x = *)
  (*   let res = *)
  (*     List.filter_map *)
  (*       (fun (y, z) -> if String.equal x y then Some z else None) *)
  (*       (get_eqlits lit) *)
  (*   in *)
  (*   match res with *)
  (*   | [] -> None *)
  (*   | [ z ] -> Some z *)
  (*   | [ _; z ] -> Some z *)
  (*   | _ -> _failatwith __FILE__ __LINE__ "die" *)

  let rec subst (y, lit) e =
    match e with
    | AC _ -> e
    | AVar x -> if String.equal x y then lit else e
    | AEq (l1, l2) -> AEq (tsubst (y, lit) l1, tsubst (y, lit) l2)
    | AAppOp (op, ls) -> AAppOp (op, List.map (tsubst (y, lit)) ls)

  and tsubst (y, lit) e : lit typed = (subst (y, lit)) #-> e

  let msubst = List.fold_right subst
  let mtsubst = List.fold_right tsubst

  (* let rec tfv (e : lit typed) = *)
  (*   let aux e = *)
  (*     match e.x with *)
  (*     | AC _ -> [] *)
  (*     | AVar x -> [ x #: e.ty ] *)
  (*     | AAppOp (_, ls) -> List.concat @@ List.map typed_fv ls *)
  (*   in *)
  (*   aux e *)

  let rec fv (e : lit) =
    let aux e =
      match e with
      | AC _ -> []
      | AVar x -> [ x ]
      | AEq (l1, l2) -> tfv l1 @ tfv l2
      | AAppOp (_, ls) -> tsfv ls
    in
    aux e

  and tfv e = fv e.x
  and tsfv ls = List.concat @@ List.map tfv ls
end

module LitRaw = struct
  module TT = F (ONt)
  include SexpCompare (TT)
  include TT
end

module Lit = struct
  module TT = F (Nt)
  include SexpCompare (TT)
  include TT
end
