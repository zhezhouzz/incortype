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
