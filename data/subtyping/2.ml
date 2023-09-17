let[@assert] rty1 ?l:(a = (true : ([%v: int][@under]))) : [%v: int] = v > a + 1
let[@assert] rty2 ?l:(a = (true : ([%v: int][@under]))) : [%v: int] = v > a + 2
