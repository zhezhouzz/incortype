let[@librty] my_size ?l:((len [@ghost]) = (true : [%v: int]) [@over])
    ?l:(_ = (size v == len : [%v: int list])) : [%v: int] =
  v == len

let rec size_gt_0 (x : int list) : int =
  match x with
  | [] -> 1
  | h :: t ->
      if h > 0 then
        let (y : int) = 1 + my_size t in
        y
      else
        let (z : int) = my_size t in
        z

let[@assert] size_gt_0 ?l:(_ = (size v > 1 : [%v: int list])) : [%v: int] =
  v > 0
