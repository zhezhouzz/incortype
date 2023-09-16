(* over -> over -> overlap *)
let[@librty] foo1 ?l:(a = (true : [%v: int]))
    ?l:(b = (not (v == a) : [%v: int])) : [%v: int] =
  v == a + b

(* over -> over -> under *)
let[@librty] foo2 ?l:(a = (true : [%v: int]))
    ?l:(b = (not (v == a) : [%v: int])) : ([%v: int][@under]) =
  v <= 10

(* over -> under -> under *)
let[@librty] foo3 ?l:(a = (true : [%v: int]))
    ?l:(b = (v <= 10 : ([%v: int][@under]))) : ([%v: int][@under]) =
  v <= 0

(* under -> under -> under *)
let[@librty] foo4 ?l:(a = (true : ([%v: int][@under])))
    ?l:(b = (v <= 10 : ([%v: int][@under]))) : ([%v: int][@under]) =
  v <= 0

(* ghost -> over -> over -> overlap *)
let[@librty] foo5 ?l:((ret [@ghost]) = (v <= 10 : [%v: int]))
    ?l:(a = (true : [%v: int]))
    ?l:(b = ((not (v == a)) && a + v == ret : [%v: int])) : ([%v: int][@under])
    =
  v == ret

(* ghost -> ghost -> over -> over -> overlap *)
let[@librty] foo6 ?l:((ret [@ghost]) = (v <= 10 : [%v: int]))
    ?l:((x [@ghost]) = (v <= 10 && v > ret : [%v: int]))
    ?l:(a = (v > x : [%v: int]))
    ?l:(b = ((not (v == a)) && a + v == ret : [%v: int])) : ([%v: int][@under])
    =
  v == ret
