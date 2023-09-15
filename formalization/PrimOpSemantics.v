From stdpp Require Import mapset.
From CT Require Import Tactics.
From CT Require Import CoreLang.
From CT Require Import CoreLangProp.
Import CoreLang.
Import Tactics.
Import NamelessTactics.

Inductive reduction : primop -> constant -> constant -> Prop :=
| rd_plus1: forall (n: nat), reduction op_plus_one n (S n)
| rd_minus1: forall (n: nat), reduction op_minus_one (S n) n
| rd_eq0: reduction op_eq_zero 0 true
| rd_eqS: forall (n: nat), reduction op_eq_zero (S n) false.

Notation "op '~' c1 '⇓' c " := (reduction op c1 c)
                                 (at level 30, format "op ~ c1 ⇓ c ", c1 constr, c constr).
