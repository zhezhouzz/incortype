type qt = Fa | Ex [@@deriving sexp]
type binary = Implies | Iff [@@deriving sexp]
type multi = And | Or [@@deriving sexp]

let multi_eq a b = match (a, b) with And, And | Or, Or -> true | _ -> false
