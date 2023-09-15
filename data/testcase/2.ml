let[@librty] bar ?l:(_ = (v > 7 : [%v: int])) : [%v: int] = v > 3

let rec foo (x : int) : int =
  let (y : int) = x + 1 in
  let (z : int) = y + 2 in
  let (w : int) = z + 3 in
  let (k : int) = bar w in
  let (p : int) = bar k in
  p

let[@assert] foo ?l:(_ = (v > 1 : [%v: int])) : [%v: int] = v > 7
