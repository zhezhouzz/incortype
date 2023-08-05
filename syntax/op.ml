module T = struct
  open Sexplib.Std

  type t = DtOp of string | BuiltinOp of string [@@deriving sexp]

  let id_eq_op = function BuiltinOp "==" -> true | _ -> false
  let id_is_dt name = String.(equal name @@ capitalize_ascii name)
  let to_string = function DtOp op -> op | BuiltinOp op -> op
  let mk_eq_op = BuiltinOp "=="
end

include Langlike.SexpCompare (T)
include T
