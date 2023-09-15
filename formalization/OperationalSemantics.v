From stdpp Require Import mapset.
From CT Require Import CoreLang.
From CT Require Import CoreLangProp.
From CT Require Import PrimOpSemantics.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.

Reserved Notation " t1 '↪' t2" (at level 60, t1 constr, t2 constr).

(** the small step operational semantics *)
Inductive step : tm -> tm -> Prop :=
| STPrimOp: forall op (c1 c: constant) e,
    body e -> lc c1 -> lc c -> op ~ c1 ⇓ c -> (tletprimop op c1 e) ↪ (e ^t^ c)
| STLetE1: forall e1 e1' e,
    body e -> e1 ↪ e1' -> (tlete e1 e) ↪ (tlete e1' e)
| STLetE2: forall (v1: value) e,
    lc v1 -> body e -> (tlete (treturn v1) e) ↪ (e ^t^ v1)
| STLetAppLam: forall T (v_x: value) e1 e,
    body e1 -> body e -> lc v_x ->
    (tletapp (vlam T e1) v_x e) ↪ tlete (e1 ^t^ v_x) e
| STLetAppFix: forall T_f (v_x: value) (e1: tm) e,
    body (vlam T_f e1) -> lc v_x -> body e ->
    tletapp (vfix T_f (vlam T_f e1)) v_x e ↪ tletapp ((vlam T_f e1) ^v^ v_x) (vfix T_f (vlam T_f e1)) e
| STMatchbTrue: forall e1 e2,
    lc e1 -> lc e2 -> (tmatchb true e1 e2) ↪ e1
| STMatchbFalse: forall e1 e2,
    lc e1 -> lc e2 -> (tmatchb false e1 e2) ↪ e2
where "t1 '↪' t2" := (step t1 t2).

Lemma step_regular: forall e1 e2,  e1 ↪ e2 -> lc e1 /\ lc e2.
Proof.
  intros.
  induction H; split; auto.
  - destruct H. econstructor; auto. apply H.
  - apply open_lc_tm; auto.
  - destruct_hyp_conj. rewrite lete_lc_body; split; auto.
  - destruct_hyp_conj. rewrite lete_lc_body; split; auto.
  - try destruct_hyp_conj. rewrite lete_lc_body; split; auto.
  - apply open_lc_tm; auto.
  - rewrite letapp_lc_body; split; auto. rewrite lc_abs_iff_body; auto.
  - rewrite lete_lc_body; split; auto. apply open_lc_tm; auto.
  - rewrite letapp_lc_body; split; auto. rewrite lc_fix_iff_body; auto.
  - rewrite letapp_lc_body; split; auto.
    + eapply open_lc_value; eauto.
    + rewrite body_vlam_eq in H. rewrite lc_fix_iff_body; eauto.
Qed.

Lemma step_regular1: forall e1 e2,  e1 ↪ e2 -> lc e1.
Proof.
  intros. apply step_regular in H. destruct H; auto.
Qed.

Lemma step_regular2: forall e1 e2,  e1 ↪ e2 -> lc e2.
Proof.
  intros. apply step_regular in H. destruct H; auto.
Qed.

Global Hint Resolve step_regular1: core.
Global Hint Resolve step_regular2: core.

Inductive multistep : tm -> tm -> Prop :=
| multistep_refl : forall (e : tm), lc e -> multistep e e
| multistep_step : forall (x y z: tm), x ↪ y -> multistep y z -> multistep x z.

Notation " t1 '↪*' t2" := (multistep t1 t2) (at level 60, t1 constr, t2 constr).

Global Hint Constructors multistep : core.

Theorem multistep_trans :
  forall (x y z : tm), x ↪* y -> y ↪* z -> x ↪* z.
Proof.
  intros. generalize dependent z. induction H; intros; eauto.
Qed.

Theorem multistep_R : forall (x y : tm),
     x ↪ y -> x ↪* y.
Proof. intros. eauto.
Qed.

Lemma multi_step_regular: forall e1 e2,  e1 ↪* e2 -> lc e1 /\ lc e2.
Proof.
  induction 1; intuition eauto.
Qed.

Lemma multi_step_regular1: forall e1 e2,  e1 ↪* e2 -> lc e1.
Proof.
  intros. apply multi_step_regular in H. destruct H; auto.
Qed.

Lemma multi_step_regular2: forall e1 e2,  e1 ↪* e2 ->  lc e2.
Proof.
  intros. apply multi_step_regular in H. destruct H; auto.
Qed.

Ltac step_regular_simp :=
  repeat match goal with
    | [H: _  _ ↪* _ |- lc _ ] => apply multi_step_regular in H; destruct H; auto
    | [H: _  _ ↪ _ |- lc _ ] => apply step_regular in H; destruct H; auto
    | [H: _  _ ↪* _ |- body _] => apply multi_step_regular in H; destruct H; auto
    | [H: _  _ ↪ _ |- body _] => apply step_regular in H; destruct H; auto
    end.


Lemma reduction_tlete:  forall e_x e (v : value),
    tlete e_x e ↪* v -> (exists (v_x: value), e_x ↪* v_x /\ (e ^t^ v_x) ↪* v).
Admitted.

Lemma reduction_mk_app_e_v (f v_x v : value) :
  lc v_x ->
  mk_app_e_v f v_x ↪* v ->
  tletapp f v_x (vbvar 0) ↪* v.
Proof.
  intros Hlc H.
  sinvert H. sinvert H0. easy.
  simpl in *. simplify_list_eq.
  rewrite open_rec_lc_value in * by eauto. eauto.
Qed.

Lemma reduction_letapplam Tb e (v_x : value) (v : value) :
  lc v_x ->
  mk_app_e_v (vlam Tb e) v_x ↪* v ->
  e ^t^ v_x ↪* v.
Proof.
  intros Hlc H.
  sinvert H.
  sinvert H0; try easy.
  simpl in H1.
  rewrite open_rec_lc_value in H1 by auto.
  sinvert H1. sinvert H.
  apply reduction_tlete in H0.
  simp_hyps. simpl in *.
Admitted.

Lemma reduction_tletapp:  forall v1 v2 e (v : value),
    tletapp v1 v2 e ↪* v ->
    (exists (v_x: value),
        mk_app_e_v v1 v2 ↪* v_x /\
          (e ^t^ v_x) ↪* v).
Admitted.

Lemma reduction_tletprimop: forall op v2 e (v : value),
    (tletprimop op v2 e) ↪* v ->
    exists (c2 c_x: constant),
      v2 = c2 /\ op ~ c2 ⇓ c_x /\  (e ^t^ c_x) ↪* v .
Proof.
  intros.
  sinvert H. sinvert H0.
  eauto 10.
Qed.

Lemma reduction_matchb_true:  forall e1 e2 (v : value),
    tmatchb true e1 e2 ↪* v -> e1 ↪* v.
Proof.
  intros.
  sinvert H.
  sinvert H0. simplify_list_eq. eauto.
Qed.

Lemma reduction_matchb_false:  forall e1 e2 (v : value),
    tmatchb false e1 e2 ↪* v -> e2 ↪* v.
Proof.
  intros.
  sinvert H.
  sinvert H0. simplify_list_eq. eauto.
Qed.
