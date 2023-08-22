open Sugar

type 'a typing_result =
  | TypeSuccess of 'a
  | TypeFailure of string * int * string

let typing_result_fmap (x : 'a typing_result) (f : 'a -> 'b) : 'b typing_result
    =
  match x with TypeFailure _ -> x | TypeSuccess x -> TypeSuccess (f x)

let typing_result_bind (x : 'a typing_result) (f : 'a -> 'b typing_result) :
    'b typing_result =
  match x with TypeFailure _ -> x | TypeSuccess x -> f x

let ( let* ) x f = typing_result_bind x f
let ( let+ ) x f = typing_result_fmap x f
let _typing_error file line err_msg = TypeFailure (file, line, err_msg)

let layout_typing_result = function
  | TypeSuccess _ -> "Type checked"
  | TypeFailure (file, line, err_msg) ->
      spf "Type error at [%s]%i: %s" file line err_msg
