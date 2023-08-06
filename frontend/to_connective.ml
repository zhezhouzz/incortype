module MetaEnv = Env
module Type = Normalty.Frontend
open Syntax
open RtyRaw.P
open Sugar
open Nt

module type T = sig
  val sym_true : string
  val sym_false : string
  val sym_and : string
  val sym_or : string
  val sym_not : string
  val sym_implies : string
  val sym_iff : string
  val sym_forall : string
  val sym_exists : string
  val sym_eq : string
  val layout_typedid : string Nt.typed -> string
end

module DetailsSetting = struct
  let sym_true = "⊤"
  let sym_false = "⊥"
  let sym_and = " ∧ "
  let sym_or = " ∨ "
  let sym_not = "¬"
  let sym_implies = "⟹"
  let sym_iff = "⟺"
  let sym_forall = "∀"
  let sym_exists = "∃"
  let sym_eq = "=="
  let layout_typedid x = spf "(%s:%s)" x.x (layout x.ty)
end

module PpSetting = struct
  let sym_true = "⊤"
  let sym_false = "⊥"
  let sym_and = " ∧ "
  let sym_or = " ∨ "
  let sym_not = "¬"
  let sym_implies = "⟹"
  let sym_iff = "⟺"
  let sym_forall = "∀"
  let sym_exists = "∃"
  let sym_eq = "="
  let layout_typedid x = x.x
end

module CoqSetting = struct
  let sym_true = "True"
  let sym_false = "False"
  let sym_and = "/\\ "
  let sym_or = " \\/ "
  let sym_not = "~"
  let sym_implies = "->"
  let sym_iff = "<->"
  let sym_forall = "forall"
  let sym_exists = "exists"
  let sym_eq = "="
  let layout_typedid x = x.x
end

module type S = sig
  include T

  val layout_qt : qt -> string
  val layout_binary : binary -> string
  val layout_multi : multi -> string
  val layout_bool : bool -> string
end

module F (T : T) : S = struct
  include T

  let layout_qt = function Fa -> sym_forall | Ex -> sym_exists
  let layout_binary = function Implies -> sym_implies | Iff -> sym_iff
  let layout_multi = function And -> sym_and | Or -> sym_or
  let layout_bool = function true -> sym_true | false -> sym_false
end

module DetailsS = F (DetailsSetting)
module PpS = F (PpSetting)
module CoqS = F (CoqSetting)
