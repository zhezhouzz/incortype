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
    | CRet of value typed
    | CLetE of { lhs : string typed; rhs : comp typed; letbody : comp typed }
    | CMatch of { matched : value typed; match_cases : match_case list }
    | CApp of { appf : value typed; apparg : value typed }
    | CAppOp of { op : Op.t typed; appopargs : value typed list }
  [@@deriving sexp]

  val do_subst_value : string * value typed -> value typed -> value typed
  val do_subst_comp : string * value typed -> comp typed -> comp typed

  val do_multisubst_value :
    (string * value typed) list -> value typed -> value typed

  val do_multisubst_comp :
    (string * value typed) list -> comp typed -> comp typed
end

module F (Ty : Typed.T) : T with type t = Ty.t and type 'a typed = 'a Ty.typed =
struct
  open Sexplib.Std
  include Ty

  type value =
    | VVar of string
    | VConst of Constant.t
    | VCont of { lamarg : string typed; contbody : comp typed }
    | VLam of { lamarg : string typed; lambody : value typed }
    | VFix of {
        fixname : string typed;
        fixarg : string typed;
        fixbody : value typed;
      }

  and match_case = {
    constructor : string typed;
    args : string typed list;
    exp : comp typed;
  }

  and comp =
    | CRet of value typed
    | CTailC of { k : value typed; apparg : value typed }
    | CLetF of {
        lhs : string typed;
        appf : value typed;
        apparg : value typed;
        letbody : comp typed;
      }
    | CLetOp of {
        lhs : string typed;
        op : Op.t typed;
        appopargs : value typed list;
        letbody : comp typed;
      }
    | CMatch of { matched : value typed; match_cases : match_case list }
  [@@deriving sexp]

  (* open Sugar *)

  open Zzdatatype.Datatype

  let rec do_subst_value (x, v) e : value typed =
    match e.x with
    | VVar y -> if String.equal x y then v else e
    | VConst _ -> e
    | VLam { lamarg; lambody } ->
        if String.equal lamarg.x x then e
        else (VLam { lamarg; lambody = do_subst_comp (x, v) lambody }) #: e.ty
    | VFix { fixname; fixarg; fixbody } ->
        if String.equal fixname.x x || String.equal fixarg.x x then e
        else
          (VFix { fixname; fixarg; fixbody = do_subst_comp (x, v) fixbody })
          #: e.ty

  and do_subst_match_case (x, v) { constructor; args; exp } =
    let exp =
      if List.exists (fun y -> String.equal x y.x) args then exp
      else do_subst_comp (x, v) exp
    in
    { constructor; args; exp }

  and do_subst_comp (x, v) e : comp typed =
    let ex =
      match e.x with
      | CRet value -> CRet (do_subst_value (x, v) value)
      | CMatch { matched; match_cases } ->
          CMatch
            {
              matched = do_subst_value (x, v) matched;
              match_cases = List.map (do_subst_match_case (x, v)) match_cases;
            }
      | CLetE { lhs; rhs; letbody } ->
          let letbody =
            if String.equal lhs.x x then letbody
            else do_subst_comp (x, v) letbody
          in
          CLetE { lhs; rhs = do_subst_comp (x, v) rhs; letbody }
      | CApp { appf; apparg } ->
          CApp
            {
              appf = do_subst_value (x, v) appf;
              apparg = do_subst_value (x, v) apparg;
            }
      | CAppOp { op; appopargs } ->
          CAppOp { op; appopargs = List.map (do_subst_value (x, v)) appopargs }
    in
    ex #: e.ty

  let do_multisubst_value (l : (string * value typed) list) (comp : value typed)
      : value typed =
    List.fold_right do_subst_value l comp

  let do_multisubst_comp (l : (string * value typed) list) (comp : comp typed) :
      comp typed =
    (* let () = *)
    (*   Printf.printf "subster list: [%s]\n" *)
    (*     (List.split_by "; " *)
    (*        (fun (x, v) -> spf "%s |--> %s" x (layout_value v)) *)
    (*        l) *)
    (* in *)
    (* let () = Printf.printf "subst %s\n" (layout_comp comp) in *)
    List.fold_right do_subst_comp l comp
end
