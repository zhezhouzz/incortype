let[@assert] rty1 ?l:(a = (true : [%v: int])) : [%v: int] = v > a + 2
let[@assert] rty2 ?l:(a = (true : [%v: int])) : [%v: int] = v > a + 1
