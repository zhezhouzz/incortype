From stdpp Require Import mapset.
From Hammer Require Export Tactics.

Ltac invclear H0 := inversion H0; subst; clear H0.

Inductive tree : Type :=
| Leaf : tree
| Node : nat -> tree -> tree -> tree.

Inductive mem: tree -> nat -> Prop :=
| mem0: forall x l r, mem (Node x l r) x
| mem1: forall x root l r, mem l x -> mem (Node root l r) x
| mem2: forall x root l r, mem r x -> mem (Node root l r) x.

Global Hint Constructors mem: core.

Lemma mem_simp: forall x root l r, mem (Node root l r) x <-> x = root \/ mem l x \/ mem r x.
Proof.
  split; intros.
  - invclear H; eauto.
  - hauto.
Qed.

Inductive ances: tree -> nat -> nat -> Prop :=
| ances0: forall x y l r, mem l y -> ances (Node x l r) x y
| ances1: forall x y l r, mem r y -> ances (Node x l r) x y
| ances2: forall x y root l r, ances l x y -> ances (Node root l r) x y
| ances3: forall x y root l r, ances r x y -> ances (Node root l r) x y.

Global Hint Constructors ances: core.

Inductive is_left: tree -> nat -> nat -> Prop :=
| is_left0: forall x y l r, mem l y -> is_left (Node x l r) x y
| is_left1: forall x y root l r, is_left l x y -> is_left (Node root l r) x y
| is_left2: forall x y root l r, is_left r x y -> is_left (Node root l r) x y.

Global Hint Constructors is_left: core.

Inductive is_right: tree -> nat -> nat -> Prop :=
| is_right0: forall x y l r, mem r y -> is_right (Node x l r) x y
| is_right1: forall x y root l r, is_right l x y -> is_right (Node root l r) x y
| is_right2: forall x y root l r, is_right r x y -> is_right (Node root l r) x y.

Global Hint Constructors is_right: core.

Inductive rep_set: tree -> Prop :=
| rep_set0: rep_set Leaf
| rep_set1: forall root l r, ~ mem l root -> ~ mem r root -> rep_set l -> rep_set r -> rep_set (Node root l r).

Global Hint Constructors rep_set: core.

Definition rep_set' (s: tree) := (forall u w, is_left s u w -> w < u) /\ (forall u w, is_right s u w -> u < w).

Lemma rep_set'_implies_rep_set: forall s, rep_set' s -> rep_set s.
Proof.
  unfold rep_set'.
  induction s; simpl; intros; auto. destruct H as (HL & HR). econstructor; eauto.
  - specialize (HL n n). intro. assert (is_left (Node n s1 s2) n n); eauto. specialize (HL H0). lia.
  - specialize (HR n n). intro. assert (is_right (Node n s1 s2) n n); eauto. specialize (HR H0). lia.
  - apply IHs1; split; intros; eauto.
  - apply IHs2; split; intros; eauto.
Qed.

Fixpoint insert (s: tree) (x: nat) :=
  match s with
  | Leaf => Node x Leaf Leaf
  | Node root l r =>
      if decide (x < root)
      then Node root (insert l x) r
      else
        if decide (x = root)
        then s
        else
          Node root l (insert r x)
  end.

Lemma insert_mem_correct: forall s x v, v = insert s x -> (forall u, mem v u <-> x = u \/ mem s u).
Proof.
  intros; subst. generalize x.
  induction s; simpl; intros; subst; simpl; eauto.
  - rewrite mem_simp. hauto.
  - case_decide; simplify_eq; simpl; eauto.
    + repeat rewrite mem_simp. hauto.
    + case_decide; simplify_eq; simpl; eauto; repeat rewrite mem_simp; hauto.
Qed.

Lemma insert_correct: forall s x v, v = insert s x -> rep_set s -> ~ mem s x -> rep_set v.
Proof.
  intros; subst. generalize dependent x.
  induction s; intros; simpl; eauto.
  inversion H0; subst.
  case_decide; simplify_eq; auto. econstructor; eauto. rewrite insert_mem_correct; eauto. hauto.
  case_decide; simplify_eq; auto. econstructor; eauto. rewrite insert_mem_correct; eauto. hauto.
Qed.

Lemma insert_correct': forall s x v, v = insert s x -> rep_set' s -> rep_set' v.
Proof.
  unfold rep_set'.
  intros; subst. generalize dependent x.
  induction s; intros; simpl; eauto.
  - split; intros; invclear H; inversion H6.
  - destruct H0.
    assert ((∀ u w : nat, is_left s1 u w → w < u) ∧ (∀ u w : nat, is_right s1 u w → u < w)) as HH.
    { split; intros; eauto. } specialize (IHs1 HH x) as (IHs1L & IHs1R). clear HH.
    assert ((∀ u w : nat, is_left s2 u w → w < u) ∧ (∀ u w : nat, is_right s2 u w → u < w)) as HH.
    { split; intros; eauto. } specialize (IHs2 HH x) as (IHs2L & IHs2R). clear HH.
    repeat case_decide; simplify_eq; auto; split; intros; eauto.
    + invclear H2; eauto. rewrite insert_mem_correct in H8; eauto. destruct H8; subst; eauto.
    + invclear H2; eauto.
    + invclear H3; eauto.
    + invclear H3; eauto. rewrite insert_mem_correct in H9; eauto. destruct H9; subst; eauto. lia.
Qed.

