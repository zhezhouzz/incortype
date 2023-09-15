From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import Qualifier.
From CT Require Import ListCtx.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import OperationalSemantics.
Import BasicTyping.
Import Qualifier.
Import ListCtx.
Import List.

(** * We define the refinement type in locally nameless style. *)

Inductive pty : Type :=
| overlap_basepty (b: base_ty) (ϕ: qualifier)
| over_basepty (b: base_ty) (ϕ: qualifier)
| under_basepty (b: base_ty) (ϕ: qualifier)
| arrpty (τ1: pty) (τ2: pty).

Global Hint Constructors pty: core.

Notation "'{:' b '|' ϕ '}'" := (over_basepty b ϕ) (at level 5, format "{: b | ϕ }", b constr, ϕ constr).
Notation "'[:' b '|' ϕ ']'" := (under_basepty b ϕ) (at level 5, format "[: b | ϕ ]", b constr, ϕ constr).
Notation "'⟨:' b '|' ϕ '⟩'" := (overlap_basepty b ϕ) (at level 5, format "⟨: b | ϕ ⟩", b constr, ϕ constr).
Notation " τ1 '⤑' τ2 " :=
  (arrpty τ1 τ2) (at level 80, format "τ1 ⤑ τ2", right associativity, τ1 constr, τ2 constr).

(** Erase *)

Fixpoint pty_erase ρ : ty :=
  match ρ with
  | {: b | _} => b
  | [: b | _] => b
  | ⟨: b | _⟩ => b
  | τ1 ⤑ τ2 => (pty_erase τ1) ⤍ (pty_erase τ2)
  end.

Class Erase A := erase : A -> ty.
#[global]
  Instance pty_erase_ : Erase pty := pty_erase.

Notation " '⌊' ty '⌋' " := (erase ty) (at level 5, format "⌊ ty ⌋", ty constr).

(** free variables *)

Fixpoint pty_fv ρ : aset :=
  match ρ with
  | {: _ | ϕ} => qualifier_fv ϕ
  | [: _ | ϕ] => qualifier_fv ϕ
  | ⟨: _ | ϕ⟩ => qualifier_fv ϕ
  |  τ1 ⤑ τ2  => (pty_fv τ1) ∪ (pty_fv τ2)
  end.

#[global]
  Instance pty_stale : @Stale aset pty := pty_fv.
Arguments pty_stale /.

Fixpoint pty_open (k: nat) (s: value) (ρ: pty) : pty :=
  match ρ with
  | {: b | ϕ } => {: b | qualifier_open (S k) s ϕ }
  | [: b | ϕ ] => [: b | qualifier_open (S k) s ϕ ]
  | ⟨: b | ϕ ⟩ => ⟨: b | qualifier_open (S k) s ϕ ⟩
  | τ1 ⤑ τ2 => (pty_open k s τ1) ⤑ (pty_open (S k) s τ2)
  end.

Notation "'{' k '~p>' s '}' e" := (pty_open k s e) (at level 20, k constr).
Notation "e '^p^' s" := (pty_open 0 s e) (at level 20).

Fixpoint pty_subst (k: atom) (s: value) (ρ: pty) : pty :=
  match ρ with
  | {: b | ϕ } => {: b | qualifier_subst k s ϕ }
  | [: b | ϕ ] => [: b | qualifier_subst k s ϕ ]
  | ⟨: b | ϕ ⟩ => ⟨: b | qualifier_subst k s ϕ ⟩
  | τ1 ⤑ τ2 => (pty_subst k s τ1) ⤑ (pty_subst k s τ2)
  end.

Notation "'{' x ':=' s '}p'" := (pty_subst x s) (at level 20, format "{ x := s }p", x constr).

(** well formed, locally closed, closed with state *)

Inductive valid_pty: pty -> Prop :=
| valid_pty_base: forall b ϕ, valid_pty ⟨: b | ϕ ⟩
| valid_over_arr: forall b ϕ τ,
    valid_pty τ -> valid_pty ({: b | ϕ } ⤑ τ)
| valid_under_arr: forall b ϕ τ,
    valid_pty τ -> valid_pty ([: b | ϕ ] ⤑ τ)
| valid_arr_arr: forall τ11 τ12 τ2,
    valid_pty (τ11 ⤑ τ12) -> valid_pty τ2 ->
    valid_pty ((τ11 ⤑ τ12) ⤑ τ2).

Inductive lc_q (ϕ: qualifier) : Prop :=
| lc_q_: forall (L : aset),
    (forall x : atom, x ∉ L -> lc_qualifier (ϕ ^q^ x)) -> lc_q ϕ.

Inductive lc_pty : pty -> Prop :=
| lc_pty_base: forall b ϕ, lc_q ϕ -> lc_pty ⟨: b | ϕ ⟩
| lc_pty_arr: forall τ1 τ2 (L : aset),
    lc_pty τ1 ->
    (forall x : atom, x ∉ L -> lc_pty (τ2 ^p^ x)) ->
    lc_pty (τ1 ⤑ τ2).

Inductive closed_pty (d : aset) (ρ: pty): Prop :=
| closed_pty_: valid_pty ρ -> lc_pty ρ -> pty_fv ρ ⊆ d -> closed_pty d ρ.

(* Type context *)

Fixpoint remove_arr_pty (Γ: listctx pty) :=
  match Γ with
  | [] => []
  | (x, (τ1 ⤑ τ2)) :: Γ => remove_arr_pty Γ
  | (x, τ) :: Γ => (x, τ) :: remove_arr_pty Γ
  end.

(* langledot *)
Notation "'⦑' x '⦒'" := (remove_arr_pty x) (at level 5, format "⦑ x ⦒", x constr).

Inductive ok_ctx: listctx pty -> Prop :=
| ok_ctx_nil: ok_ctx []
| ok_ctx_cons: forall (Γ: listctx pty)(x: atom) (ρ: pty),
    ok_ctx Γ ->
    closed_pty (ctxdom ⦑ Γ ⦒) ρ ->
    x ∉ ctxdom Γ ->
    ok_ctx (Γ ++ [(x, ρ)]).

Definition ctx_closed_pty (Γ: listctx pty) :=
  forall Γ1 (x: atom) (ρ: pty) Γ2, Γ = Γ1 ++ [(x, ρ)] ++ Γ2 -> closed_pty (ctxdom ⦑ Γ1 ⦒) ρ.

Lemma ok_ctx_ok: forall Γ, ok_ctx Γ -> ok Γ.
Proof.
  induction 1; eauto.
Qed.

Definition ctx_erase (Γ: listctx pty) :=
  ⋃ ((List.map (fun e => {[e.1 := pty_erase e.2]}) Γ): list (amap ty)).

Notation " '⌊' Γ '⌋*' " := (ctx_erase Γ) (at level 5, format "⌊ Γ ⌋*", Γ constr).

(** Ty Function *)
Definition mk_eq_constant c := ⟨: ty_of_const c | b0:c= c ⟩.
Definition mk_eq_var ty (x: atom) := ⟨: ty | b0:x= x ⟩.

Lemma pty_erase_open_eq ρ : forall k s,
    pty_erase ρ = pty_erase ({k ~p> s} ρ).
Proof.
  induction ρ; intros; eauto.
  cbn. f_equal; eauto.
Qed.

Lemma pty_erase_subst_eq ρ: forall x s,
  pty_erase ρ = pty_erase ({x := s}p ρ).
Proof.
  induction ρ; intros; eauto.
  cbn. f_equal; eauto.
Qed.

Lemma ctx_erase_lookup Γ x ρ :
  ctxfind Γ x = Some ρ -> ⌊Γ⌋* !! x = Some ⌊ρ⌋.
Proof.
  induction Γ; simpl; intros; try easy.
  destruct a. case_decide. simplify_eq.
  cbn. simplify_map_eq. reflexivity.
  simp_hyps.
  cbn. rewrite insert_empty. rewrite <- insert_union_singleton_l.
  simplify_map_eq. reflexivity.
Qed.

Lemma ctx_erase_app Γ Γ':
  ⌊Γ ++ Γ'⌋* = ⌊Γ⌋* ∪ ⌊Γ'⌋*.
Proof.
  induction Γ; simpl.
  - cbn. by rewrite map_empty_union.
  - destruct a. unfold ctx_erase in *. cbn. rewrite IHΓ.
    by rewrite map_union_assoc.
Qed.

Lemma ctx_erase_dom Γ :
  dom ⌊Γ⌋* ≡ ctxdom Γ.
Proof.
  induction Γ; simpl.
  - cbn. apply dom_empty.
  - destruct a. cbn in *.
    rewrite insert_empty.
    setoid_rewrite dom_union.
    rewrite dom_singleton.
    f_equiv. eauto.
Qed.

Lemma ctx_erase_app_r Γ x ρ :
  x # Γ ->
  ⌊Γ ++ [(x, ρ)]⌋* = <[x:=⌊ρ⌋]> ⌊Γ⌋*.
Proof.
  intros H.
  rewrite ctx_erase_app.
  cbn. rewrite map_union_empty. rewrite insert_empty.
  rewrite <- insert_union_singleton_r. auto.
  simpl in H. rewrite <- ctx_erase_dom in H.
  by apply not_elem_of_dom.
Qed.


Lemma subst_fresh_pty: forall (ρ: pty) (x:atom) (u: value),
    x # ρ -> {x := u}p ρ = ρ.
Proof.
  intros.
  induction ρ;
    simpl in *; f_equal; eauto using subst_fresh_qualifier;
  auto_apply; my_set_solver.
Qed.

Lemma subst_commute_pty : forall x u_x y u_y ρ,
    x <> y -> x ∉ fv_value u_y -> y ∉ fv_value u_x ->
    {x := u_x }p ({y := u_y }p ρ) = {y := u_y }p ({x := u_x }p ρ).
Proof.
  intros.
  induction ρ; simpl; f_equal;
    eauto using subst_commute_qualifier.
Qed.

Lemma open_fv_pty' (ρ : pty) (v : value) k :
  pty_fv ρ ⊆ pty_fv ({k ~p> v} ρ).
Proof.
Admitted.

Lemma remove_arr_pty_ctx_dom_union Γ Γ' :
  ctxdom ⦑ Γ ++ Γ' ⦒ = ctxdom ⦑ Γ ⦒ ∪ ctxdom ⦑ Γ' ⦒.
Proof.
  induction Γ; intros; simpl.
  my_set_solver.
  destruct a. case_split; eauto.
  simpl. rewrite <- union_assoc_L. f_equal. eauto.
Admitted.

Lemma remove_arr_pty_ctx_dom_app_commute Γ Γ' :
  ctxdom ⦑ Γ ++ Γ' ⦒ = ctxdom ⦑ Γ' ++ Γ ⦒.
Proof.
  rewrite !remove_arr_pty_ctx_dom_union.
  my_set_solver.
Qed.

Lemma remove_arr_pty_ctx_dom_singleton x v :
  ctxdom ⦑ [(x, v)] ⦒ ⊆ {[x]}.
Proof.
  simpl. case_split; simpl; my_set_solver.
Qed.

Lemma remove_arr_pty_ctx_dom_subseteq Γ :
  ctxdom ⦑ Γ ⦒ ⊆ ctxdom Γ.
Proof.
  induction Γ; intros; simpl. my_set_solver.
  repeat case_split; simpl; my_set_solver.
Qed.

Lemma open_subst_same_qualifier: forall x y (ϕ : qualifier) k,
    x # ϕ ->
    {x := y }q ({k ~q> x} ϕ) = {k ~q> y} ϕ.
Proof.
  destruct ϕ. cbn. intros.
  f_equal. clear - H.
  (* A better proof should simply reduce to vector facts. Don't bother yet. *)
  induction vals; cbn; eauto.
  cbn in H.
  f_equal. apply open_subst_same_value. my_set_solver.
  apply IHvals. my_set_solver.
Qed.

Lemma open_subst_same_pty: forall x y (ρ : pty) k,
    x # ρ ->
    {x := y }p ({k ~p> x} ρ) = {k ~p> y} ρ.
Proof.
Admitted.

Lemma subst_open_qualifier: forall (ϕ: qualifier) (x:atom) (u: value) (w: value) (k: nat),
    lc w -> {x := w}q ({k ~q> u} ϕ) = ({k ~q> {x := w}v u} ({x := w}q ϕ)).
Proof.
  destruct ϕ. cbn. intros.
  f_equal.
  rewrite !Vector.map_map.
  apply Vector.map_ext.
  eauto using subst_open_value.
Qed.

Lemma subst_open_pty: forall (ρ: pty) (x:atom) (u: value) (w: value) (k: nat),
    lc w -> {x := w}p ({k ~p> u} ρ) = ({k ~p> {x := w}v u} ({x := w}p ρ)).
Proof.
Admitted.

Lemma subst_open_qualifier_closed:
  ∀ (ϕ : qualifier) (x : atom) (u w : value) (k : nat),
    closed_value u ->
    lc w → {x := w }q ({k ~q> u} ϕ) = {k ~q> u} ({x := w }q ϕ).
Proof.
  intros. rewrite subst_open_qualifier; auto.
  rewrite (subst_fresh_value); eauto. set_solver.
Qed.

Lemma subst_open_pty_closed:
  ∀ (ρ : pty) (x : atom) (u w : value) (k : nat),
    closed_value u ->
    lc w → {x := w }p ({k ~p> u} ρ) = {k ~p> u} ({x := w }p ρ).
Proof.
  intros. rewrite subst_open_pty; auto.
  rewrite (subst_fresh_value); eauto. set_solver.
Qed.

Lemma subst_lc_qualifier : forall x (u: value) (ϕ: qualifier),
    lc_qualifier ϕ -> lc u -> lc_qualifier ({x := u}q ϕ).
Proof.
  destruct 1. intros Hu.
  econstructor.
  srewrite Vector.to_list_Forall.
  rewrite Vector.to_list_map.
  rewrite Forall_map.
  eapply Forall_impl; eauto.
  simpl. eauto using subst_lc_value.
Qed.

Lemma subst_open_var_qualifier: forall x y (u: value) (ϕ: qualifier) (k: nat),
    x <> y -> lc u -> {x := u}q ({k ~q> y} ϕ) = ({k ~q> y} ({x := u}q ϕ)).
Proof.
  intros.
  rewrite subst_open_qualifier; auto. simpl. rewrite decide_False; auto.
Qed.

Lemma subst_open_var_pty: forall x y (u: value) (ρ: pty) (k: nat),
    x <> y -> lc u -> {x := u}p ({k ~p> y} ρ) = ({k ~p> y} ({x := u}p ρ)).
Proof.
  intros.
  rewrite subst_open_pty; auto. simpl. rewrite decide_False; auto.
Qed.

Lemma subst_lc_pty : forall x (u: value) (ρ: pty),
    lc_pty ρ -> lc u -> lc_pty ({x := u}p ρ).
Proof.
Admitted.

Lemma fv_of_subst_qualifier:
  forall x (u : value) (ϕ: qualifier),
    qualifier_fv ({x := u }q ϕ) ⊆ (qualifier_fv ϕ ∖ {[x]}) ∪ fv_value u.
Proof.
  destruct ϕ; simpl. clear. induction vals; simpl.
  my_set_solver.
  etrans.
  apply union_mono_r.
  apply fv_of_subst_value.
  my_set_solver.
Qed.

Lemma fv_of_subst_pty:
  forall x (u : value) (ρ: pty),
    pty_fv ({x := u }p ρ) ⊆ (pty_fv ρ ∖ {[x]}) ∪ fv_value u.
Proof.
Admitted.

Lemma fv_of_subst_pty_closed:
  forall x (u : value) (ρ: pty),
    closed_value u ->
    pty_fv ({x := u }p ρ) ⊆ (pty_fv ρ ∖ {[x]}).
Proof.
  intros.
  rewrite fv_of_subst_pty.
  my_set_solver.
Qed.

Lemma open_not_in_eq_qualifier (x : atom) (ϕ : qualifier) k :
  x # {k ~q> x} ϕ ->
  forall e, ϕ = {k ~q> e} ϕ.
Proof.
  destruct ϕ. simpl. intros.
  f_equal.
  clear - H.
  induction vals; simpl; eauto.
  f_equal. apply open_not_in_eq_value with x. my_set_solver.
  auto_apply. my_set_solver.
Qed.

Lemma open_not_in_eq_pty (x : atom) (ρ : pty) k :
  x # {k ~p> x} ρ ->
  forall e, ρ = {k ~p> e} ρ.
Proof.
Admitted.

Lemma subst_intro_pty: forall (ρ: pty) (x:atom) (w: value) (k: nat),
    x # ρ ->
    lc w -> {x := w}p ({k ~p> x} ρ) = ({k ~p> w} ρ).
Proof.
  intros.
  specialize (subst_open_pty ρ x x w k) as J.
  simpl in J. rewrite decide_True in J; auto.
  rewrite J; auto. rewrite subst_fresh_pty; auto.
Qed.

Lemma lc_subst_qualifier:
  forall x (u: value) (ϕ: qualifier), lc_qualifier ({x := u}q ϕ) -> lc u -> lc_qualifier ϕ.
Proof.
  intros.
  sinvert H.
  destruct ϕ. simpl in *. simplify_eq.
  econstructor.
  srewrite Vector.to_list_Forall.
  srewrite Vector.to_list_map.
  srewrite Forall_map.
  eapply Forall_impl; eauto.
  simpl. eauto using lc_subst_value.
Qed.

Lemma lc_subst_pty: forall x (u: value) (ρ: pty), lc_pty ({x := u}p ρ) -> lc u -> lc_pty ρ.
Proof.
Admitted.

Lemma open_rec_lc_qualifier: forall (v: value) (ϕ: qualifier) (k: nat),
    lc_qualifier ϕ -> {k ~q> v} ϕ = ϕ.
Proof.
  destruct 1. simpl. f_equal.
  rewrite <- Vector.map_id.
  apply Vector.map_ext_in.
  rewrite Vector.Forall_forall in H.
  eauto using open_rec_lc_value.
Qed.

Lemma subst_intro_qualifier: forall (ϕ: qualifier) (x:atom) (w: value) (k: nat),
    x # ϕ ->
    lc w -> {x := w}q ({k ~q> x} ϕ) = ({k ~q> w} ϕ).
Proof.
  intros.
  specialize (subst_open_qualifier ϕ x x w k) as J.
  simpl in J. rewrite decide_True in J; auto.
  rewrite J; auto. rewrite subst_fresh_qualifier; auto.
Qed.

Lemma open_lc_qualifier: forall (u: value) (ϕ: qualifier),
    (* don't body defining body yet. *)
    (exists L : aset, forall x : atom, x ∉ L -> lc_qualifier (ϕ ^q^ x)) ->
    lc u ->
    lc_qualifier ({0 ~q> u} ϕ).
Proof.
  intros. destruct H.
  let acc := collect_stales tt in pose acc.
  pose (Atom.fv_of_set a).
  assert (a0 ∉ a). apply Atom.fv_of_set_fresh.
  erewrite <- subst_intro_qualifier; auto. instantiate (1:= a0).
  apply subst_lc_qualifier; auto. apply H.
  my_set_solver. my_set_solver.
Qed.

Lemma open_swap_qualifier: forall (ϕ: qualifier) i j (u v: value),
    lc u ->
    lc v ->
    i <> j ->
    {i ~q> v} ({j ~q> u} ϕ) = {j ~q> u} ({i ~q> v} ϕ).
Proof.
  destruct ϕ. intros. simpl.
  f_equal. rewrite !Vector.map_map.
  apply Vector.map_ext.
  eauto using open_swap_value.
Qed.

Lemma open_lc_respect_qualifier: forall (ϕ: qualifier) (u v : value) k,
    lc_qualifier ({k ~q> u} ϕ) ->
    lc u ->
    lc v ->
    lc_qualifier ({k ~q> v} ϕ).
Proof.
  intros. sinvert H.
  destruct ϕ. simpl in *. simplify_eq.
  econstructor.
  srewrite Vector.to_list_Forall.
  rewrite Vector.to_list_map in *.
  rewrite Forall_map in *.
  eapply Forall_impl; eauto.
  simpl. eauto using open_lc_respect_value.
Qed.
