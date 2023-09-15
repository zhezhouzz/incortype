let[@librty] ( == ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  v == (a == b)

let[@librty] ( != ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  v == (a != b)

let[@librty] ( < ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  v == (a < b)

let[@librty] ( > ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  v == (a > b)

let[@librty] ( <= ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  v == (a <= b)

let[@librty] ( >= ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: bool] =
  v == (a >= b)

let[@librty] ( + ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == a + b

let[@librty] ( - ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == a - b

let[@librty] ( mod ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == a mod b

let[@librty] ( * ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (true : [%v: int]) [@over]) : [%v: int] =
  v == a * b

let[@librty] ( / ) ?l:(a = (true : [%v: int]) [@over])
    ?l:(b = (not (v == 0) : [%v: int]) [@over]) : [%v: int] =
  v == a / b

let[@librty] _True = (v : [%v: bool])
let[@librty] _False = (not v : [%v: bool])
let[@librty] _Nil = (0 == size v : [%v: int list])

let[@librty] _Cons ?l:(h = (true : [%v: int]) [@over])
    ?l:(t = (true : [%v: int list]) [@over]) : [%v: int list] =
  (fun (u : [%forall: int]) -> iff (mem v u) (u == h || mem t u))
  && iff (set_rep v) ((not (mem t h)) && set_rep t)
