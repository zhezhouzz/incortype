From stdpp Require Import mapset.
From Coq Require Import Lists.List.
From Hammer Require Export Tactics.
Import List.
Import ListNotations.

Definition mem (s: list nat) (x: nat) := In x s.

Inductive rep_set: list nat -> Prop :=
| rep_set0: rep_set []
| rep_set1: forall h: nat, forall t: list nat, ~ In h t -> rep_set t -> rep_set (h :: t).

Global Hint Constructors rep_set: core.

Inductive strict_sorted: list nat -> Prop :=
| strict_sorted0: strict_sorted []
| strict_sorted1: forall h: nat, forall t: list nat, (forall u, In u t -> h < u) -> strict_sorted t -> strict_sorted (h :: t).

Global Hint Constructors strict_sorted: core.

Fixpoint insert_v1 (s: list nat) (x: nat) :=
  match s with
  | [] => [x]
  | h :: t => if decide (h = x) then s else h :: (insert_v1 t x)
  end.

Fixpoint insert_v2 (s: list nat) (x: nat) :=
  match s with
  | [] => [x]
  | h :: t =>
      if decide (x < h)
      then x :: s
      else
        if decide (h = x)
        then s
        else
          h :: (insert_v2 t x)
  end.

Lemma insert_v1_mem_correct: forall s x v, v = insert_v1 s x -> (forall u, mem v u <-> x = u \/ mem s u).
Proof.
  unfold mem.
  intro s. induction s; simpl; intros; subst; eauto.
  case_decide; simplify_eq; simpl; hauto.
Qed.

Lemma insert_v1_correct: forall s x v, v = insert_v1 s x -> rep_set s -> rep_set v /\ (forall u, mem v u <-> x = u \/ mem s u).
Proof.
  intros. split; try apply insert_v1_mem_correct; auto.
  subst. generalize x. induction s; intros; simpl; eauto.
  case_decide; simplify_eq; auto. inversion H0; subst; clear H0.
  econstructor; eauto. setoid_rewrite insert_v1_mem_correct; eauto. hauto.
Qed.

Lemma insert_v2_mem_correct: forall s x v, v = insert_v2 s x -> (forall u, mem v u <-> x = u \/ mem s u).
Proof.
  intros; subst. generalize dependent x. unfold mem.
  induction s; simpl; intros; subst; eauto.
  hauto.
Qed.

Ltac invclear H0 := inversion H0; subst; clear H0.

Lemma insert_v2_correct: forall s x v, v = insert_v2 s x -> strict_sorted s -> strict_sorted v.
Proof.
  intros; subst. generalize dependent x.
  induction s; intros; simpl; eauto.
  - econstructor; hauto.
  - inversion H0; subst. specialize (IHs H3 x).
    case_decide; simplify_eq; auto. econstructor; hauto.
    case_decide; simplify_eq; auto. econstructor; eauto.
    setoid_rewrite insert_v2_mem_correct; hauto.
Qed.

Lemma insert_v2_correct': forall s x v, v = insert_v2 s x -> rep_set s -> ~ mem s x -> rep_set v.
Proof.
  intros; subst. generalize dependent x.
  induction s; intros; simpl; eauto.
  inversion H0; subst. specialize (IHs H4 x).
  case_decide; simplify_eq; auto.
  case_decide; simplify_eq; auto.
  econstructor; eauto.
  - setoid_rewrite insert_v2_mem_correct; hauto.
  - hauto.
Qed.
