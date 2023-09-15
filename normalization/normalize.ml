open Language
module T = Structure
open TypedCore
open Sugar
open Zzdatatype.Datatype

type cont = rhs typed -> comp typed
type vcont = value typed -> comp typed
type vconts = value typed list -> comp typed

let new_x () = Rename.unique "x"
let construct_letv lhs rhs letbody = (CLet { lhs; rhs; letbody }) #: letbody.ty
let var_to_v x = (VVar x.x) #: x.ty

(* let vcont_to_cont (k : value typed -> comp typed) (rhs : value typed) : *)
(*     comp typed = *)
(*   let lhs = (new_x ()) #: rhs.ty in *)
(*   construct_letv lhs rhs (k (var_to_v lhs)) *)

let rec normalize_term (tm : T.term T.typed) : comp typed =
  normalize_name (fun v -> (CVal v.x) #: v.ty) tm

and normalize (k' : cont) (expr : T.term T.typed) : comp typed =
  let k e = k' e #: expr.ty in
  match expr.x with
  | T.Err -> k CErr
  | T.Tu _ -> _failatwith __FILE__ __LINE__ "die"
  | T.Var var -> k (CRhsV (VVar var))
  | T.Const c -> k (CRhsV (VConst c))
  | T.Lam { lamarg; lambody } ->
      k (CRhsV (VLam { lamarg; lambody = normalize_term lambody }))
  | T.(Let { if_rec; lhs; rhs; letbody }) -> (
      match (if_rec, lhs) with
      | true, fixname :: args ->
          let fixbody =
            List.fold_left
              (fun lambody lamarg -> T.mk_lam lamarg lambody)
              rhs args
          in
          normalize_name
            (fun v ->
              let v' =
                match v.x with
                | VLam { lamarg; lambody } ->
                    VFix { fixname; fixarg = lamarg; fixbody = lambody }
                | _ -> _failatwith __FILE__ __LINE__ "die"
              in
              let rhs = (CRhsV v') #: v.ty in
              construct_letv fixname rhs (normalize k' letbody))
            fixbody
      | true, _ -> _failatwith __FILE__ __LINE__ "bad"
      | false, [] -> _failatwith __FILE__ __LINE__ "bad"
      | false, [ lhs ] ->
          normalize
            (fun rhs -> construct_letv lhs rhs (normalize k' letbody))
            rhs
      | false, _ -> _failatwith __FILE__ __LINE__ "die")
  | T.(AppOp (op, es)) ->
      normalize_names (fun appopargs -> k (CAppOp { op; appopargs })) es
  | T.(App (_, [])) -> _failatwith __FILE__ __LINE__ "die"
  | T.(App (func, [ arg ])) ->
      normalize_name
        (fun appf ->
          normalize_name (fun apparg -> k (CApp { appf; apparg })) arg)
        func
  | T.(App _) -> _failatwith __FILE__ __LINE__ "die"
  | T.(Ite (cond, et, ef)) ->
      normalize k'
        T.(
          (Match
             ( cond,
               [
                 { constructor = "True" #: bool_ty; args = []; exp = et };
                 { constructor = "False" #: bool_ty; args = []; exp = ef };
               ] ))
          #: expr.ty)
  | T.(Match (matched, match_cases)) ->
      normalize_name
        (fun matched ->
          let match_cases =
            List.map
              (fun T.{ constructor; args; exp } ->
                { constructor; args; exp = normalize k' exp })
              match_cases
          in
          (CMatch { matched; match_cases }) #: expr.ty)
        matched

and normalize_name (k : vcont) (expr : T.term T.typed) : comp typed =
  normalize
    (fun e ->
      match e.x with
      | CRhsV v -> k v #: e.ty
      | _ ->
          let lhs = (new_x ()) #: e.ty in
          construct_letv lhs e (k @@ var_to_v lhs))
    expr

and normalize_names (k : vconts) (es : T.term T.typed list) : comp typed =
  (List.fold_left
     (fun (k : vconts) rhs ids -> normalize_name (fun id -> k (id :: ids)) rhs)
     k es)
    []

module S = Language.Structure

let get_normalized_code code =
  S.filter_map_imps
    (fun name if_rec body ->
      let body = normalize_term body in
      let e = if if_rec then lam_to_fix_comp name #: body.ty body else body in
      Some (name, e))
    code
