From stdpp Require Import mapset.
From Hammer Require Export Tactics.

Ltac invclear H0 := inversion H0; subst; clear H0.

Inductive ltree : Type :=
| Leaf : ltree
| Node : nat -> ltree -> nat -> ltree -> ltree.

(* Inductive rank_of_root: ltree -> nat -> Prop := *)
(* | rank0: rank_of_root Leaf 0 *)
(* | rank1: forall rank l root r n, rank_of_root r n -> rank_of_root (Node rank l root r) (S n). *)

Fixpoint rank_of_root (s: ltree) :=
  match s with
  | Leaf => 0
  | Node _ _ _ r => S (rank_of_root r)
  end.

Inductive rep_leftist: ltree -> Prop :=
| rep_leftist0: rep_leftist Leaf
| rep_leftist1: forall rank l root r,
    rank = S (rank_of_root r) -> rank_of_root r <= rank_of_root l ->
    rep_leftist l -> rep_leftist r ->
    rep_leftist (Node rank l root r).

Global Hint Constructors rep_leftist: core.

Lemma rep_leftist_nonzero: forall a1 x b1, ~ rep_leftist (Node 0 a1 x b1).
Proof.
  intros. intro H. invclear H. inversion H4. Qed.

Inductive mem: ltree -> nat -> Prop :=
| mem0: forall rank x l r, mem (Node rank l x r) x
| mem1: forall rank x root l r, mem l x -> mem (Node rank l root r) x
| mem2: forall rank x root l r, mem r x -> mem (Node rank l root r) x.

Global Hint Constructors mem: core.

Inductive ances: ltree -> nat -> nat -> Prop :=
| ances0: forall x y rank l r, mem l y -> ances (Node rank l x r) x y
| ances1: forall x y rank l r, mem r y -> ances (Node rank l x r) x y
| ances2: forall x y rank root l r, ances l x y -> ances (Node rank l root r) x y
| ances3: forall x y rank root l r, ances r x y -> ances (Node rank l root r) x y.

Global Hint Constructors ances: core.

Lemma ances_simp: forall x y rank root l r,
    ances (Node rank l root r) x y <-> x = root /\ (mem l y \/ mem r y) \/ ances l x y \/ ances r x y.
Proof.
  split; intros.
  - invclear H; eauto.
  - hauto.
Qed.

Lemma mem_simp: forall x rank root l r, mem (Node rank l root r) x <-> x = root \/ mem l x \/ mem r x.
Proof.
  split; intros.
  - invclear H; eauto.
  - hauto.
Qed.

Inductive is_left: ltree -> nat -> nat -> Prop :=
| is_left0: forall x y rank l r, mem l y -> is_left (Node rank l x r) x y
| is_left1: forall x y rank root l r, is_left l x y -> is_left (Node rank l root r) x y
| is_left2: forall x y rank root l r, is_left r x y -> is_left (Node rank l root r) x y.

Global Hint Constructors is_left: core.

Inductive is_right: ltree -> nat -> nat -> Prop :=
| is_right0: forall x y rank l r, mem r y -> is_right (Node rank l x r) x y
| is_right1: forall x y rank root l r, is_right l x y -> is_right (Node rank l root r) x y
| is_right2: forall x y rank root l r, is_right r x y -> is_right (Node rank l root r) x y.

Global Hint Constructors is_right: core.

(* Inductive rep_set: ltree -> Prop := *)
(* | rep_set0: rep_set Leaf *)
(* | rep_set1: forall rank root l r, ~ mem l root -> ~ mem r root -> rep_set l -> rep_set r -> rep_set (Node rank l root r). *)

(* Global Hint Constructors rep_set: core. *)

(* Definition rep_set' (s: ltree) := (forall u w, is_left s u w -> w < u) /\ (forall u w, is_right s u w -> u < w). *)

(* Lemma rep_set'_implies_rep_set: forall s, rep_set' s -> rep_set s. *)
(* Proof. *)
(*   unfold rep_set'. *)
(*   induction s; simpl; intros; auto. destruct H as (HL & HR). econstructor; eauto. *)
(*   - specialize (HL n n). intro. assert (is_left (Node n s1 s2) n n); eauto. specialize (HL H0). lia. *)
(*   - specialize (HR n n). intro. assert (is_right (Node n s1 s2) n n); eauto. specialize (HR H0). lia. *)
(*   - apply IHs1; split; intros; eauto. *)
(*   - apply IHs2; split; intros; eauto. *)
(* Qed. *)

Definition hd (s: ltree) (x: nat) : Prop :=
  match s with
  | Leaf => False
  | Node _ _ y _ => x = y
  end.

Definition rank (s: ltree) : nat :=
  match s with
  | Leaf => 0
  | Node rank _ _ _ => rank
  end.

Lemma rank_of_root_0: forall h1, rank_of_root h1 = 0 <-> h1 = Leaf.
Proof. destruct h1; hauto. Qed.

Lemma rep_leftist_implies_rank: forall h, rep_leftist h -> rank_of_root h = rank h.
Proof.
  induction h. hauto.
  intros. invclear H. simpl. hauto.
Qed.

Ltac rank_simpl :=
  repeat match goal with
    | H: context [ rank_of_root (Node _ _ _ _)] |- _ => rewrite rep_leftist_implies_rank in H; auto; simpl in H; subst
    | |- context [ rank_of_root (Node _ _ _ _)] => rewrite rep_leftist_implies_rank; auto; simpl; subst
    end.

(* Inductive merge: ltree -> ltree -> ltree -> Prop := *)
(* | merge0: forall h2, merge Leaf h2 h2 *)
(* | merge1: forall h1, merge h1 Leaf h1 *)
(* | merge2: forall rank1 a1 x b1 rank2 a2 b2 h3, *)
(*     rank2 <= rank b1 -> *)
(*     merge b1 (Node rank2 a2 x b2) h3 -> *)
(*     merge (Node rank1 a1 x b1) (Node rank2 a2 x b2) (makeT x a1 h3) *)
(* | merge22: forall rank1 a1 x b1 rank2 a2 b2 h3, *)
(*     rank b1 < rank2 -> *)
(*     merge (Node rank2 a2 x b2) b1 h3 -> *)
(*     merge (Node rank1 a1 x b1) (Node rank2 a2 x b2) (makeT x a1 h3) *)
(* | merge3: forall rank1 a1 x b1 rank2 a2 y b2 h3, *)
(*     ~ x = y -> *)
(*     merge (Node rank1 a1 x b1) b2 h3 -> *)
(*     merge (Node rank1 a1 x b1) (Node rank2 a2 y b2) (makeT y a2 h3). *)

(* Inductive merge: ltree -> ltree -> ltree -> Prop := *)
(* | merge0: forall h2, merge Leaf h2 h2 *)
(* | merge1: forall h1, merge h1 Leaf h1 *)
(* | merge2: forall rank1 a1 x b1 rank2 a2 b2 h3, *)
(*     merge b1 (Node rank2 a2 x b2) h3 -> *)
(*     merge (Node rank1 a1 x b1) (Node rank2 a2 x b2) (Node (S rank1) h3 x a1) *)
(* | merge3: forall rank1 a1 x b1 rank2 a2 y b2 h3, *)
(*     ~ x = y -> *)
(*     merge (Node rank1 a1 x b1) b2 h3 -> *)
(*     merge (Node rank1 a1 x b1) (Node rank2 a2 y b2) (makeT y a2 h3). *)

(* Fixpoint merge (h1 h2: ltree) : ltree := *)
(*   match h1 with *)
(*   | Leaf => h2 *)
(*   | Node rank1 a1 x b1 => *)
(*       match h2 with *)
(*       | Leaf => h1 *)
(*       | Node rank2 a2 y b2 => *)
(*           if decide (x <= y) *)
(*           then Node (S rank1) (merge b1 h2) x a1 *)
(*           else makeT y a2 (merge h1 b2) *)
(*       end *)
(*   end. *)

Fixpoint merge_to_left (h1 h2: ltree): ltree :=
  match h1 with
  | Leaf => h2
  | Node rank l x r => Node rank (merge_to_left l h2) x r
  end.

Definition rep_heap (h1: ltree) := (forall u w, ances h1 u w -> u <= w).

Inductive rep_heap_prop: ltree -> Prop :=
| rep_heap_prop0: rep_heap_prop Leaf
| rep_heap_prop1: forall n0 h1_1 n1 h1_2,
    rep_heap_prop h1_1 -> rep_heap_prop h1_2 -> (forall u, mem h1_1 u \/ mem h1_2 u -> n1 <= u) ->
    rep_heap_prop (Node n0 h1_1 n1 h1_2).

Global Hint Constructors rep_heap_prop: core.

Lemma rep_heap_prop_same: forall h, rep_heap_prop h <-> rep_heap h.
Admitted.

Lemma rep_heap_simp: forall n0 h1_1 n1 h1_2,
    rep_heap (Node n0 h1_1 n1 h1_2) <-> rep_heap h1_1 /\ rep_heap h1_2 /\ (forall u, mem h1_1 u \/ mem h1_2 u -> n1 <= u).
Proof.
  intros. repeat rewrite <- rep_heap_prop_same. split; intros.
  - invclear H. hauto.
  - econstructor; eauto; hauto.
Qed.

Lemma merge_to_left_leftist_correct: forall (h1 h2: ltree),
    rep_leftist h1 -> rep_leftist h2 -> rep_leftist (merge_to_left h1 h2).
Proof.
  induction h1; simpl; intros; auto. clear IHh1_2.
  invclear H.
  econstructor; eauto.  clear - H6.
  destruct h1_1; auto. simpl in H6. lia.
Qed.

Lemma merge_to_left_member_correct: forall (h1 h2: ltree), forall u, mem (merge_to_left h1 h2) u <-> mem h1 u \/ mem h2 u.
Proof.
  induction h1; simpl; split; intros; subst; invclear H; eauto.
  - inversion H0.
  - hauto.
  - invclear H0; eauto. econstructor; hauto.
  - econstructor. hauto.
Qed.

Lemma merge_to_left_heap_correct: forall (h1 h2: ltree),
    rep_heap h1 -> rep_heap h2 -> (forall u w, mem h1 u -> mem h2 w -> u <= w) -> rep_heap (merge_to_left h1 h2).
Proof.
  unfold rep_heap. induction h1; simpl; intros; auto. invclear H2; eauto.
  - rewrite merge_to_left_member_correct in H9. destruct H9; eauto.
  - eapply IHh1_1; eauto.
Qed.

Definition makeT (x: nat) (a: ltree) (b: ltree) :=
  if decide ((rank b) <= (rank a))
  then Node (S (rank b)) a x b
  else Node (S (rank a)) b x a.

Fixpoint size (h: ltree) : nat :=
  match h with
  | Leaf => 0
  | Node _ l _ r => 1 + size l + size r
  end.

Fixpoint merge (size: nat) (h1 h2: ltree): ltree :=
  match size with
  | 0 => Leaf
  | S size =>
      match h1 with
      | Leaf => h2
      | Node _ a1 x b1 =>
          match h2 with
          | Leaf => h1
          | Node _ a2 y b2 =>
              if decide (x <= y)
              then makeT x a1 (merge size b1 h2)
              else makeT y a2 (merge size b2 h1)
          end
      end
  end.

Lemma size0_implies_empty: forall h1, size h1 ≤ 0 -> h1 = Leaf.
Proof.
  destruct h1; simpl; intro; auto. lia.
Qed.

Lemma makeT_member_correct: forall x (h1 h2: ltree), forall u, mem (makeT x h1 h2) u <-> u = x \/ mem h1 u \/ mem h2 u.
Proof.
  unfold makeT; intros x h1 h2. destruct h1, h2; simpl;
    repeat case_decide; simplify_eq; simpl; eauto;
    repeat setoid_rewrite mem_simp; intros; eauto; hauto.
Qed.

Lemma merge_member_correct: forall n (h1 h2: ltree), size h1 + size h2 <= n -> forall u, mem (merge n h1 h2) u <-> mem h1 u \/ mem h2 u.
Proof.
  induction n; split; simpl; intros; eauto.
  - invclear H0.
  - destruct h1, h2; simpl in H; eauto; try lia. hauto.
  - destruct h1, h2; auto.
    repeat case_decide; simplify_eq; simpl; eauto; rewrite makeT_member_correct in H0.
    + rewrite IHn in H0; eauto. hauto. simpl. simpl in H. lia.
    + rewrite IHn in H0; eauto. hauto. simpl. simpl in H. lia.
  - destruct h1, h2; auto. hauto. destruct H0; eauto. inversion H0. destruct H0; eauto. inversion H0.
    repeat rewrite mem_simp in H0.
    repeat case_decide; simplify_eq; simpl; eauto; rewrite makeT_member_correct.
    + repeat rewrite mem_simp; rewrite IHn; eauto. hauto. hauto.
    + repeat rewrite mem_simp; rewrite IHn; eauto. hauto. hauto.
Qed.

Lemma makeT_heap_correct: forall (h1 h2: ltree) x,
    (forall u, mem h1 u -> x <= u) ->
    (forall u, mem h2 u -> x <= u) ->
    rep_heap h1 -> rep_heap h2 -> rep_heap (makeT x h1 h2).
Proof.
  unfold rep_heap; unfold makeT; destruct h1, h2; simpl; intros; eauto; repeat case_decide; simplify_eq; simpl; eauto;
  rewrite ances_simp in H3; try hauto.
Qed.

Lemma merge_heap_correct: forall n (h1 h2: ltree),
    size h1 + size h2 <= n ->
    rep_heap h1 -> rep_heap h2 -> rep_heap (merge n h1 h2).
Proof.
  induction n; simpl; intros; eauto.
  - destruct h1, h2; simpl in H; eauto; try lia.
  - destruct h1, h2; auto. simpl in H.
    rewrite rep_heap_simp in H0. rewrite rep_heap_simp in H1.
    repeat case_decide; simplify_eq; simpl; eauto.
    + apply makeT_heap_correct; eauto; try hauto.
      * intros. rewrite merge_member_correct in H3; simpl; eauto; try lia.
        rewrite mem_simp in H3.
        destruct H3. hauto. destruct H3. hauto. assert (n3 <= u) by hauto. lia.
      * apply IHn; eauto. simpl. lia. hauto. rewrite rep_heap_simp; hauto.
    + apply makeT_heap_correct; eauto; try hauto.
      * intros. rewrite merge_member_correct in H3; simpl; eauto; try lia.
        rewrite mem_simp in H3.
        destruct H3. hauto. destruct H3. hauto. assert (n1 <= u) by hauto. lia.
      * apply IHn; eauto. simpl. lia. hauto. rewrite rep_heap_simp; hauto.
Qed.

Lemma makeT_leftist_correct: forall (h1 h2: ltree) x,
    rep_leftist h1 -> rep_leftist h2 -> rep_leftist (makeT x h1 h2).
Proof.
  unfold makeT; destruct h1, h2; simpl; intros; eauto; repeat case_decide; simplify_eq; simpl; econstructor; rank_simpl; eauto; try lia.
  - invclear H0; invclear H; auto.
  - invclear H0; invclear H; auto. lia.
Qed.

Lemma merge_leftist_correct: forall n (h1 h2: ltree),
    size h1 + size h2 <= n ->
    rep_leftist h1 -> rep_leftist h2 -> rep_leftist (merge n h1 h2).
Proof.
  induction n; simpl; intros; eauto.
  destruct h1, h2; auto. simpl in H. invclear H0. invclear H1.
    repeat case_decide; simplify_eq; simpl; eauto; apply makeT_leftist_correct; eauto.
    + apply IHn; eauto. simpl. lia.
    + apply IHn; eauto. simpl. lia.
Qed.
