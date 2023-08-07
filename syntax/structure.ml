open Langlike

module F (L : Lit.T) = struct
  include Termlang.F (L)
  module R = Rty.F (L)

  type rty_kind = RtyLib | RtyToCheck

  type entry =
    | Type_dec of Type_dec.t
    | Func_dec of string Normalty.Ntyped.typed
    | FuncImp of { name : string; if_rec : bool; body : term typed }
    | Rty of { name : string; kind : rty_kind; rty : R.rty }

  type structure = entry list

  (* open Sugar *)
  open Zzdatatype.Datatype

  let mk_normal_opctx_ = function
    | FuncImp _ -> []
    | Rty _ -> []
    | Func_dec x -> [ (Op.BuiltinOp x.x, x.ty) ]
    | Type_dec d -> List.map (fun Nt.{ x; ty } -> (x, ty)) @@ Type_dec.mk_ctx_ d

  let mk_normal_opctx es = List.concat @@ List.map mk_normal_opctx_ es

  let mk_normal_ctx_ = function
    | FuncImp _ -> []
    | Rty { name; kind; rty } -> (
        match kind with
        | RtyLib -> [ (name, R.erase_rty rty) ]
        | RtyToCheck -> [])
    | Func_dec _ -> []
    | Type_dec _ -> []

  let mk_normal_ctx es = List.concat @@ List.map mk_normal_ctx_ es

  let map_imps f codes =
    List.map
      (fun code ->
        match code with
        | FuncImp { name; if_rec; body } ->
            FuncImp { name; if_rec; body = f name if_rec body }
        | _ -> code)
      codes

  let map_rtys f codes =
    List.map
      (fun code ->
        match code with
        | Rty { name; kind; rty } -> Rty { name; kind; rty = f rty }
        | _ -> code)
      codes

  let get_lib_rtys codes =
    List.filter
      (fun code ->
        match code with Rty { kind = RtyLib; _ } -> true | _ -> false)
      codes

  let get_assert_rtys codes =
    List.filter
      (fun code ->
        match code with Rty { kind = RtyToCheck; _ } -> true | _ -> false)
      codes

  let get_imps codes =
    List.filter
      (fun code -> match code with FuncImp _ -> true | _ -> false)
      codes

  let filter_map_imps f codes =
    List.filter_map
      (fun code ->
        match code with
        | FuncImp { name; if_rec; body } -> f name if_rec body
        | _ -> None)
      codes
end
