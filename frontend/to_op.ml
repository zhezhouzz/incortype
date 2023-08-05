open Syntax.Op

let op_to_string = function
  | DtOp "Cons" -> "::"
  | DtOp "Nil" -> "[]"
  | DtOp dt -> dt
  | BuiltinOp f -> f

let op_to_paring_string = function
  | DtOp dt -> String.lowercase_ascii dt
  | BuiltinOp f -> f

let string_to_op name =
  match name with
  | "[]" -> Some (DtOp "Nil")
  | "::" -> Some (DtOp "Cons")
  | _ ->
      if String.length name > 0 then
        let code = Char.code @@ String.get name 0 in
        if 65 <= code && code <= 90 then Some (DtOp name)
        else Some (BuiltinOp name)
      else None
