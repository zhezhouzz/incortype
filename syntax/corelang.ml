module type T = sig
  include Typed.T

  type value =
    | VVar of string
    | VConst of Constant.t
    | VLam of { lamarg : string typed; lambody : comp typed }
    | VFix of {
        fixname : string typed;
        fixarg : string typed;
        fixbody : comp typed;
      }

  and match_case = {
    constructor : string typed;
    args : string typed list;
    exp : comp typed;
  }

  and comp =
    | CErr
    | CVal of value
    | CLetE of { lhs : string typed; rhs : comp typed; letbody : comp typed }
    | CMatch of { matched : value typed; match_cases : match_case list }
    | CApp of { appf : value typed; apparg : value typed }
    | CAppOp of { op : Op.t typed; appopargs : value typed list }
  [@@deriving sexp]

  (* aux *)
  val mk_lam : string typed -> comp typed -> value typed
  val mk_fix : string typed -> string typed -> comp typed -> value typed
  val mk_lete : string typed -> comp typed -> comp typed -> comp typed
  val mk_app : value typed -> value typed -> comp typed
  val lam_to_fix_comp : string typed -> comp typed -> comp typed

  (* cast *)
  val to_value : comp -> value
  val to_comp : value -> comp
  val tto_value : comp typed -> value typed
  val tto_comp : value typed -> comp typed
  val tcomp_to_str : comp typed -> string typed
  val tvalue_to_str : value typed -> string typed

  (* subst *)
  val subst_value : string * value typed -> value typed -> value typed
  val subst_comp : string * value typed -> comp typed -> comp typed
  val msubst_value : (string * value typed) list -> value typed -> value typed
  val msubst_comp : (string * value typed) list -> comp typed -> comp typed
end

module F (Ty : Typed.T) : T with type t = Ty.t and type 'a typed = 'a Ty.typed =
struct
  open Sexplib.Std
  include Ty

  type value =
    | VVar of string
    | VConst of Constant.t
    | VLam of { lamarg : string typed; lambody : comp typed }
    | VFix of {
        fixname : string typed;
        fixarg : string typed;
        fixbody : comp typed;
      }

  and match_case = {
    constructor : string typed;
    args : string typed list;
    exp : comp typed;
  }

  and comp =
    | CErr
    | CVal of value
    | CLetE of { lhs : string typed; rhs : comp typed; letbody : comp typed }
    | CMatch of { matched : value typed; match_cases : match_case list }
    | CApp of { appf : value typed; apparg : value typed }
    | CAppOp of { op : Op.t typed; appopargs : value typed list }
  [@@deriving sexp]

  open Sugar

  let to_value = function
    | CVal x -> x
    | _ -> _failatwith __FILE__ __LINE__ "not a value"

  let tto_value x = to_value #-> x
  let to_comp v = CVal v
  let tto_comp v = to_comp #-> v

  let value_to_str = function
    | VVar x -> x
    | _ -> _failatwith __FILE__ __LINE__ "not a var"

  let tvalue_to_str x = value_to_str #-> x

  let comp_to_str = function
    | CVal (VVar x) -> x
    | _ -> _failatwith __FILE__ __LINE__ "not a var"

  let tcomp_to_str x = comp_to_str #-> x

  let mk_lam (lamarg : string typed) (lambody : comp typed) : value typed =
    (VLam { lamarg; lambody }) #: (mk_arr lamarg.ty lambody.ty)

  let mk_fix (fixname : string typed) (fixarg : string typed)
      (fixbody : comp typed) : value typed =
    (VFix { fixname; fixarg; fixbody }) #: fixname.ty

  let mk_lete lhs rhs letbody = (CLetE { lhs; rhs; letbody }) #: letbody.ty
  let mk_app appf apparg = (CApp { appf; apparg }) #: (get_retty appf.ty)

  let lam_to_fix fixname (body : value typed) : value typed =
    match body.x with
    | VLam { lamarg; lambody } -> mk_fix fixname lamarg lambody
    | _ -> _failatwith __FILE__ __LINE__ ""

  let lam_to_fix_comp fixname (body : comp typed) : comp typed =
    tto_comp (lam_to_fix fixname (tto_value body))

  open Zzdatatype.Datatype

  let rec subst_value (x, v) e : value typed =
    match e.x with
    | VVar y -> if String.equal x y then v else e
    | VConst _ -> e
    | VLam { lamarg; lambody } ->
        if String.equal lamarg.x x then e
        else (VLam { lamarg; lambody = subst_comp (x, v) lambody }) #: e.ty
    | VFix { fixname; fixarg; fixbody } ->
        if String.equal fixname.x x || String.equal fixarg.x x then e
        else
          (VFix { fixname; fixarg; fixbody = subst_comp (x, v) fixbody })
          #: e.ty

  and subst_match_case (x, v) { constructor; args; exp } =
    let exp =
      if List.exists (fun y -> String.equal x y.x) args then exp
      else subst_comp (x, v) exp
    in
    { constructor; args; exp }

  and subst_comp (x, v) e : comp typed =
    let ex =
      match e.x with
      | CErr -> CErr
      | CVal value -> CVal (subst_value (x, v) value #: e.ty).x
      | CMatch { matched; match_cases } ->
          CMatch
            {
              matched = subst_value (x, v) matched;
              match_cases = List.map (subst_match_case (x, v)) match_cases;
            }
      | CLetE { lhs; rhs; letbody } ->
          let letbody =
            if String.equal lhs.x x then letbody else subst_comp (x, v) letbody
          in
          CLetE { lhs; rhs = subst_comp (x, v) rhs; letbody }
      | CApp { appf; apparg } ->
          CApp
            {
              appf = subst_value (x, v) appf;
              apparg = subst_value (x, v) apparg;
            }
      | CAppOp { op; appopargs } ->
          CAppOp { op; appopargs = List.map (subst_value (x, v)) appopargs }
    in
    ex #: e.ty

  let msubst_value = List.fold_right subst_value

  let msubst_comp (l : (string * value typed) list) (comp : comp typed) :
      comp typed =
    (* let () = *)
    (*   Printf.printf "subster list: [%s]\n" *)
    (*     (List.split_by "; " *)
    (*        (fun (x, v) -> spf "%s |--> %s" x (layout_value v)) *)
    (*        l) *)
    (* in *)
    (* let () = Printf.printf "subst %s\n" (layout_comp comp) in *)
    List.fold_right subst_comp l comp
end
