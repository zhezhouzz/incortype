From stdpp Require Import stringmap mapset.

(** We use the string as variables in the core langauge *)
Definition atom := string.
Definition amap := stringmap.
Definition aset := stringset.

(** The Stale will gather all free variables in type context, values, terms... *)
Class Stale {D} A := stale : A -> D.

Definition fv_of_set (s: aset): atom := fresh_string_of_set "x" s.
Lemma fv_of_set_fresh (s: aset) : (fv_of_set s) ∉ s.
Proof.
  apply fresh_string_of_set_fresh.
Qed.

Definition atom_dec: ∀ s1 s2 : atom, {s1 = s2} + {s1 ≠ s2} := string_dec.
Definition atom_eqb: atom → atom → bool := String.eqb.
Definition atom_eqb_spec (s1 s2 : atom): reflect (s1 = s2) (atom_eqb s1 s2) := String.eqb_spec s1 s2.

Parameter value : Type.
Inductive term : Type :=
| Tret (v: value)
| Tother (e: term).
Parameter step :  term -> value -> Prop.
Parameter term_subst : atom -> value -> term -> Prop.

Lemma step_value: forall v, step (Tret v) v.
Admitted.

Definition denotation (phi: value -> Prop) (e: term) := exists v, step e v /\ phi v.

Lemma denotation_implies (phi1 phi2: value -> Prop): (forall v, phi1 v -> phi2 v) -> (forall e, denotation phi1 e -> denotation phi2 e).
Proof.
  unfold denotation. intros.
  destruct H0 as (v & Hstep & H1). exists v. split; auto.
Qed.

Definition ctx_denotation (phi_fa: value -> Prop) (phi_ex: value -> value -> Prop) (phi: value -> value -> value -> Prop) (e: term) :=
  forall v1, phi_fa v1 -> exists v2, phi_ex v1 v2 /\ denotation (phi v1 v2) e.

Definition ctx_denotation_e (phi_ex: value -> Prop) (phi_fa: value -> value -> Prop) (e: term) :=
  exists v1, phi_ex v1 /\ forall v, phi_fa v1 v -> step e v.

Definition subtyping (phi_ex: value -> Prop) (phi1 phi2: value -> value -> Prop) :=
  exists x_ex, phi_ex x_ex /\
            forall v2, phi2 x_ex v2 ->
                  exists v1, phi1 x_ex v1 /\
                          forall v, v = v1 -> v = v2.

Definition subtyping_sound (phi_ex: value -> Prop): forall (phi1 phi2: value -> value -> Prop),
    subtyping phi_ex phi1 phi2 ->
    (forall e, ctx_denotation_e phi_ex phi1 e -> ctx_denotation_e phi_ex phi2 e).
Proof.
  unfold subtyping, ctx_denotation_e. intros.
  destruct H as (x_ex)
  specialize (H _ H1). specialize (H0 _ H1).
  (* destruct H as (x_ex & Hex & H). *)
  destruct H0 as (x_ex & Hex & H0).
  exists x_ex. split; auto.
  eapply denotation_implies with (phi1 x_fa x_ex); eauto.
  specialize (H _ Hex). destruct H as (v22 & Hex2 & HHH).
  exists v22. split; auto. eapply denotation_implies; eauto.
Qed.


Definition ctx_denotation_e (phi_ex: value -> Prop) (phi_fa: value -> value -> Prop) (phi: value -> value -> value -> Prop) (e: term) :=
  exists v1, phi_ex v1 /\ forall v2, phi_fa v1 v2 -> denotation (phi v1 v2) e.

Definition subtyping_e (phi_ex: value -> Prop) (phi_fa: value -> value -> Prop) (phi1 phi2: value -> value -> value -> Prop) :=
  forall x_fa, phi_ex x_fa -> exists x_ex, phi_fa v11 v12 /\ exists v21, phi_ex v21 /\ forall v22, phi_fa v21 v22 -> (forall e, phi1 v11 v12 e -> phi2 v21 v22 e).

Definition subtyping_sound (phi_ex: value -> Prop) (phi_fa: value -> value -> Prop): forall (phi1 phi2: value -> value -> value -> Prop),
    subtyping_e phi_ex phi_fa phi1 phi2 -> (forall e, ctx_denotation_e phi_ex phi_fa phi1 e -> ctx_denotation_e phi_ex phi_fa phi2 e).
Proof.
  unfold subtyping_e, ctx_denotation_e. intros.
  destruct H0 as (v11 & H11 & H0). specialize (H _ H11).
  destruct H as (v12 & H12 & H). specialize (H0 _ H12).
  destruct H as (v21 & H21 & H). exists v21. split; auto.
  intros. apply denotation_implies with (phi1 v11 v12); eauto.
Qed.

Definition Prop1 := value -> Prop.
Definition Prop2 := value -> value -> Prop.
Definition Prop3 := value -> value -> value -> Prop.

Inductive typectx : Type :=
| Empty
| Fa (p: Prop1) (ctx: value -> typectx)
| Ex (p: Prop1) (ctx: value -> typectx).

Inductive ctx_denotation: typectx -> (list value -> Prop) -> Prop:=
| ctx_denotation0: forall (P: list value -> Prop), P [] -> ctx_denotation Empty P
| ctx_denotation1: forall (p: Prop1) ctx (P: list value -> Prop),
    (forall v, p v -> ctx_denotation (ctx v) (fun tl => P (v :: tl))) ->
    ctx_denotation (Fa p ctx) P
| ctx_denotation2: forall (p: Prop1) ctx (P: list value -> Prop),
    (exists v, p v /\ ctx_denotation (ctx v) (fun tl => P (v :: tl))) ->
    ctx_denotation (Ex p ctx) P.

Inductive subtyping : typectx -> (list value -> value -> Prop) -> (list value -> value -> Prop) -> Prop :=
| subtyping0: forall (p1 p2: list value -> value -> Prop), (forall v, p1 [] v -> p2 [] v) -> subtyping Empty p1 p2
| subtyping1: forall (p1 p2: list value -> value -> Prop), (forall v, p1 [] v -> p2 [] v) -> subtyping Empty p1 p2


                                                           (ctx: typectx) (p1 p2: list value -> value -> Prop)


Definition ctx_denotation (phi_fa: value -> Prop) (phi_ex: value -> value -> Prop) (phi: value -> value -> value -> Prop) (e: term) :=
  forall v1, phi_fa v1 -> exists v2, phi_ex v1 v2 /\ denotation (phi v1 v2) e.

Definition subtyping  (phi_fa: value -> Prop) (phi_ex: value -> value -> Prop) (phi1 phi2: value -> value -> value -> Prop) :=
  forall v1, phi_fa v1 -> forall v21, phi_ex v1 v21 -> exists v22, phi_ex v1 v22 /\ (forall e, phi1 v1 v21 e -> phi2 v1 v22 e).

Definition subtyping_sound (phi_fa: value -> Prop) (phi_ex: value -> value -> Prop): forall (phi1 phi2: value -> value -> value -> Prop),
    subtyping phi_fa phi_ex phi1 phi2 -> (forall e, ctx_denotation phi_fa phi_ex phi1 e -> ctx_denotation phi_fa phi_ex phi2 e).
Proof.
  unfold subtyping, ctx_denotation. intros.
  specialize (H _ H1). specialize (H0 _ H1). destruct H0 as (v21 & Hex & HH).
  specialize (H _ Hex). destruct H as (v22 & Hex2 & HHH).
  exists v22. split; auto. eapply denotation_implies; eauto.
Qed.
