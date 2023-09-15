let rec foo (x : int) : int =
  let (y : int) = foo (if x == 0 then x - (x + 1) else x - 9) in
  foo y + foo y

let rec foo (x : int) (y : int) : int = (if x > 0 then foo y else foo x) x
let rec foo (x : int) (y : int) : int = (if x > 0 then foo y else Err) x
