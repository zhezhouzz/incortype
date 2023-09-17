let[@assert] rty1 ?l:(a = (v > 0 : ([%v: int][@under]))) : [%v: int] = v > a
let[@assert] rty2 ?l:(a = (v > 0 : ([%v: int][@under]))) : [%v: int] = v > 0
