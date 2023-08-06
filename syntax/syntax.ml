(* parsing only *)
include Langlike
module LRaw = Lit.LitRaw
module L = Lit.Lit
module StructureRaw = Structure.F (LRaw)
module Structure = Structure.F (L)
module RtyRaw = StructureRaw.R
module Rty = Structure.R

(* unwrap *)
module Const = Constant
module Op = Op
module Type_dec = Type_dec
module Typectx = Typectx
module Corelang = Corelang
