module type T = sig
  include Typed.T

  type term =
    | Var of string
    | Const of Constant.t
    | Lam of { lamarg : string typed; lambody : term typed }
    (* term *)
    | Err
    | Let of {
        if_rec : bool;
        lhs : string typed list;
        rhs : term typed;
        letbody : term typed;
      }
    | App of term typed * term typed list
    | AppOp of Op.t typed * term typed list
    | Ite of term typed * term typed * term typed
    | Tu of term typed list
    | Match of term typed * match_case list

  and match_case = {
    constructor : string typed;
    args : string typed list;
    exp : term typed;
  }
  [@@deriving sexp]

  (* for parsing *)
  val mk_var : string -> term typed
  val mk_unit : term typed
  val mk_bool : bool -> term typed
  val mk_int : int -> term typed

  (* cast *)
  val to_var : term -> string
  val tto_var : term typed -> string typed
  val to_var_opt : term -> string option
  val tto_var_opt : term typed -> string typed option

  (* curry *)
  val uncurry : term typed -> string typed list * term typed
  val curry : string typed list * term typed -> term typed
  val de_typed_tuple : term typed -> term typed list
  val mk_lam : string typed -> term typed -> term typed
end

module F (Ty : Typed.T) : T with type t = Ty.t and type 'a typed = 'a Ty.typed =
struct
  open Sexplib.Std
  include Ty

  type term =
    | Var of string
    | Const of Constant.t
    | Lam of { lamarg : string typed; lambody : term typed }
    (* term *)
    | Err
    | Let of {
        if_rec : bool;
        lhs : string typed list;
        rhs : term typed;
        letbody : term typed;
      }
    | App of term typed * term typed list
    | AppOp of Op.t typed * term typed list
    | Ite of term typed * term typed * term typed
    | Tu of term typed list
    | Match of term typed * match_case list

  and match_case = {
    constructor : string typed;
    args : string typed list;
    exp : term typed;
  }
  [@@deriving sexp]

  open Sugar

  let mk_var name = mk_noty @@ Var name
  let mk_bool b = (Const (Constant.B b)) #: bool_ty
  let mk_unit = (Const Constant.U) #: unit_ty
  let mk_int i = (Const (Constant.I i)) #: int_ty
  let to_var_opt = function Var x -> Some x | _ -> None

  let tto_var_opt { x; ty } =
    let* x = to_var_opt x in
    Some { x; ty }

  let to_var x = _deopt __FUNCTION__ @@ to_var_opt x
  let tto_var { x; ty } = { x = to_var x; ty }

  let uncurry tm =
    let rec aux args = function
      | { x = Lam { lamarg; lambody }; _ } -> aux (args @ [ lamarg ]) lambody
      | e -> (args, e)
    in
    aux [] tm

  let curry (args, body) =
    List.fold_right
      (fun lamarg lambody ->
        (Lam { lamarg; lambody }) #: (mk_arr lamarg.ty lambody.ty))
      args body

  let de_typed_tuple { x; ty } = match x with Tu es -> es | _ -> [ { x; ty } ]

  let mk_lam (lamarg : string typed) (lambody : term typed) : term typed =
    (Lam { lamarg; lambody }) #: (mk_arr lamarg.ty lambody.ty)
end
