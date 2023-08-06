open Syntax
module R = LRaw
open L
open Coersion_aux

let rec force_typed lit = _force __FILE__ __LINE__ R.(force #-> lit)

and force lit =
  match lit with
  | R.AC c -> AC c
  | R.AVar x -> AVar x
  | R.AEq (x, y) -> AEq (force_typed x, force_typed y)
  | R.AAppOp (f, args) ->
      AAppOp (_force __FILE__ __LINE__ f, List.map force_typed args)

let rec besome_typed lit = _besome besome #-> lit

and besome lit =
  match lit with
  | AC c -> R.AC c
  | AVar x -> R.AVar x
  | AEq (x, y) -> R.AEq (besome_typed x, besome_typed y)
  | AAppOp (f, args) -> R.AAppOp (_besome f, List.map besome_typed args)
