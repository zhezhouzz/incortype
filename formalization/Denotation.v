From stdpp Require Import mapset.
From stdpp Require Import natmap.
From Coq.Program Require Import Wf.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import RefinementType.
From CT Require Import Instantiation.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import ListCtx.
Import OperationalSemantics.
Import BasicTyping.
Import RefinementType.
Import Qualifier.
Import PrimOpSemantics.
Import mapset.

(** Type Denotation: *)

Definition singleton (P: tm -> Prop) := exists e, forall e', P e' <-> e = e'.

Definition mk_app_e_v_P (Pe: tm -> Prop) (v: value) := fun e' => exists e, Pe e /\ e' = (mk_app_e_v e v).

Fixpoint ptyR (ρ: pty) (Pe: tm -> Prop) : Prop :=
  (forall e, Pe e -> ∅ ⊢t e ⋮t ⌊ ρ ⌋) /\ closed_pty ∅ ρ /\
    match ρ with
    | {: b | ϕ } =>
        singleton Pe /\ (forall (v: constant), Pe v -> denote_qualifier (ϕ ^q^ v))
    | [: b | ϕ ] =>
        (forall (v: constant), ∅ ⊢t v ⋮t b -> denote_qualifier (ϕ ^q^ v) -> Pe v)
    | ⟨: b | ϕ⟩ =>
        (exists e (v: constant), Pe e /\ e ↪* v /\ ∅ ⊢t v ⋮t b /\ denote_qualifier (ϕ ^q^ v))
    | τ1 ⤑ τ2 =>
        forall (P1: tm -> Prop),
          ptyR τ1 P1 ->
          exists (e1: tm) (v1: value),  P1 e1 /\ e1 ↪* v1 /\ ptyR τ2 (mk_app_e_v_P Pe v1)
    end.

Notation "'⟦' ρ '⟧' " :=
  (ptyR ρ) (at level 20, format "⟦ ρ ⟧", ρ constr).

Notation "'m{' x '}q'" := (msubst qualifier_subst x) (at level 20, format "m{ x }q", x constr).
Notation "'m{' x '}p'" := (msubst pty_subst x) (at level 20, format "m{ x }p", x constr).
Notation "'m{' x '}v'" := (msubst value_subst x) (at level 20, format "m{ x }v", x constr).
Notation "'m{' x '}t'" := (msubst tm_subst x) (at level 20, format "m{ x }t", x constr).

Definition prefix: Type := (env -> Prop) -> Prop.

Inductive ctxRst: listctx pty -> prefix -> Prop :=
| ctxRst0: ctxRst [] (fun prop => prop ∅)
| ctxRst1: forall Γ (x: atom) τ (pf: prefix),
    ok_ctx (Γ ++ [(x, τ)]) ->
    ctxRst Γ pf ->
    ctxRst (Γ ++ [(x, τ)])
      (fun (prop: env -> Prop) =>
         pf
           (fun (env: env) =>
              (forall (Px: tm -> Prop), ⟦ m{ env }p τ ⟧ Px ->
                               exists (e_x: tm) (v_x: value), Px e_x /\ e_x ↪* v_x /\ prop (<[ x := v_x ]> env)))).

Lemma ctxRst_closed_env Γ pf : ctxRst Γ pf -> pf (fun Γv => closed_env Γv).
Admitted.

Lemma ctxRst_lc Γ pf :
  ctxRst Γ pf -> pf (fun Γv => map_Forall (fun _ v => lc (treturn v)) Γv).
Admitted.

Lemma ctxRst_dom Γ pf :
  ctxRst Γ pf -> pf (fun Γv => ctxdom Γ ≡ dom Γv).
Admitted.

Lemma ctxRst_ok_ctx Γ Γv :
  ctxRst Γ Γv -> ok_ctx Γ.
Proof.
  induction 1; eauto. econstructor.
Qed.
