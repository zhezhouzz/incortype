From stdpp Require Import mapset.
From Coq Require Import Logic.ClassicalFacts.
From Coq Require Import Classical.
From CT Require Import CoreLang.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import OperationalSemantics.
Import BasicTyping.
Import PrimOpSemantics.

Notation env := (amap value).

Definition closed_env (env : env) := map_Forall (fun _ => closed_value) env.

Definition msubst {A} (subst : atom -> value -> A -> A)
                  (env : env) (a : A) : A :=
  map_fold subst a env.

Definition instantiation (Γ: amap ty) (Γv: env) :=
  forall (x: atom),
    match Γ !! x with
    | None => Γv !! x = None
    | Some T =>
      match Γv !! x with
      | None => False
      | Some v => ∅ ⊢t v ⋮v T
      end
    end.

Definition termRraw Γ e e' :=
  forall Γv (v: value), instantiation Γ Γv ->
                   msubst tm_subst Γv e ↪* v ->
                   msubst tm_subst Γv e' ↪* v.

Inductive termR: amap ty -> ty -> tm -> tm -> Prop :=
| termR_c: forall Γ T (e e': tm),
    Γ ⊢t e ⋮t T -> Γ ⊢t e' ⋮t T ->
    termRraw Γ e e' ->
    termR Γ T e e'.

Notation " e1 '<-<{' Γ ';' T '}' e2 " :=
  (termR Γ T e1 e2) (at level 10, format "e1 <-<{ Γ ; T } e2", Γ constr, T constr).

Notation " e1 '<-<{' Γ '}' e2 " :=
  (termRraw Γ e1 e2) (at level 10, format "e1 <-<{ Γ } e2", Γ constr).

Lemma termRraw_refl: forall Γ e, e <-<{ Γ } e.
Proof.
  intros. intro; auto.
Qed.

Lemma termR_refl: forall Γ e T, Γ ⊢t e ⋮t T -> e <-<{ Γ ; T } e.
Proof.
  intros. constructor; auto. intro; auto.
Qed.

Lemma closed_env_insert env x v :
  env !! x = None ->
  closed_env (<[x:=v]>env) ->
  closed_value v /\ closed_env env.
Proof.
  intro.
  unfold closed_env.
  rewrite map_Forall_insert; eauto.
Qed.
