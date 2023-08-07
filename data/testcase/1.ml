let[@librty] foo1 ?l:(a = (true : [%v: int]))
    ?l:(b = (not (v == a) : [%v: int])) : [%v: int] =
  v == a + b

let[@librty] foo2 ?l:(a = (true : [%v: int]))
    ?l:(b = (not (v == a) : [%v: int])) : [%v: int] =
  v == a + b

let[@librty] foo3 ?l:(a = (true : [%v: int]))
    ?l:(b = (not (v == a) : [%v: int])) : [%v: int] =
  v == a + b

let[@librty] foo4 ?l:(a = (true : [%v: int]))
    ?l:(b = (not (v == a) : [%v: int])) : [%v: int] =
  v == a + b

let rec foo (x : int) : int =
  let (y : int) = if x == 0 then x - (x + 1) else x - 9 in
  foo y + foo (foo y)
