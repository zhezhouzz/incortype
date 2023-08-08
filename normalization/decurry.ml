open Language
open Structure
open Sugar
open Zzdatatype.Datatype

let rec decurry_func f = function
  | [] -> f
  | arg :: args -> decurry_func (App (f, [ arg ])) #: (get_retty f.ty) args

let rec decurry_term (e : term) : term =
  match e with
  | Var _ | Const _ | Err -> e
  | Lam { lamarg; lambody } -> Lam { lamarg; lambody = decurry_tterm lambody }
  | Let { if_rec; lhs; rhs; letbody } ->
      Let
        {
          if_rec;
          lhs;
          rhs = decurry_tterm rhs;
          letbody = decurry_tterm letbody;
        }
  | App (f, args) ->
      let f = decurry_tterm f in
      let args = List.map decurry_tterm args in
      (decurry_func f args).x
  | AppOp (op, args) -> AppOp (op, List.map decurry_tterm args)
  | Ite (e1, e2, e3) ->
      Ite (decurry_tterm e1, decurry_tterm e2, decurry_tterm e3)
  | Tu _ -> _failatwith __FILE__ __LINE__ "die"
  | Match (matched, cases) ->
      Match (decurry_tterm matched, List.map decurry_matched_case cases)

and decurry_matched_case { constructor; args; exp } =
  { constructor; args; exp = decurry_tterm exp }

and decurry_tterm (e : term typed) : term typed = decurry_term #-> e

let deccury_code code = map_imps (fun _ _ body -> decurry_tterm body) code
