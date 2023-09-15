From stdpp Require Import mapset.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import RefinementType.
From CT Require Import Denotation.
From CT Require Import DenotationProp.
From CT Require Import Instantiation.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import ListCtx.
Import PrimOpSemantics.
Import OperationalSemantics.
Import BasicTyping.
Import RefinementType.
Import Denotation.
Import DenotationProp.
Import Instantiation.
Import Qualifier.

Notation " Γ '⊢WF' τ " := (closed_pty (ctxdom ⦑ Γ ⦒) τ) (at level 20, τ constr, Γ constr).

Inductive fork_ctx : listctx pty -> pty -> pty -> listctx pty -> Prop :=
| fork_ctx0: forall (τ1 τ2: pty), fork_ctx [] τ1 τ2 []
| fork_ctx1: forall (x y: atom) b ϕ (τ1 τ2: pty) (Γ Γ': listctx pty),
    ok_ctx ([(y, {:b | ϕ}); (x, [:b | ϕ])] ++ Γ') ->
    fork_ctx (List.map (fun binding => (binding.1 , {x := y}p binding.2)) Γ) ({x := y}p τ1) τ2 Γ' ->
    fork_ctx ([(x, [:b | ϕ])] ++ Γ) τ1 τ2 ([(y, {:b | ϕ}); (x, [:b | ϕ])] ++ Γ').

Definition subtyping (Γ: listctx pty) (τ1 τ2: pty) : Prop :=
  forall Γ', fork_ctx Γ τ1 τ2 Γ' ->
        forall pf, ctxRst Γ' pf ->
              pf (fun Γv => forall Pe, ⟦(m{ Γv }p) τ1⟧ (fun e => Pe (m{ Γv }t e)) -> ⟦(m{ Γv }p) τ2⟧ (fun e => Pe (m{ Γv }t e))).

Notation " Γ '⊢' τ1 '<⋮' τ2 " := (subtyping Γ τ1 τ2) (at level 20, τ1 constr, τ2 constr, Γ constr).

Lemma pf_implies Γ (pf: prefix):
  ctxRst Γ pf -> forall (P P': env -> Prop), (forall (Γv: env), closed_env Γv -> P Γv -> P' Γv) -> pf P -> pf P'.
Proof.
  induction 1; intros; eauto. apply H; eauto. admit.
  eapply IHctxRst; eauto.
  intros. edestruct H4; eauto. mydestr. exists x0, x1. do 2 (split; eauto). apply H1; eauto. admit.
Admitted.

Lemma subtyping_soundness (Γ: listctx pty):
  forall (τ1 τ2: pty),
    subtyping Γ τ1 τ2 ->
    forall (Pe: tm -> Prop),
      (forall pf, ctxRst Γ pf -> pf (fun Γv => ⟦(m{ Γv }p) τ1⟧ (fun e => Pe (m{ Γv }t e)))) ->
      (forall pf, ctxRst Γ pf -> pf (fun Γv => ⟦(m{ Γv }p) τ2⟧ (fun e => Pe (m{ Γv }t e)))).
Proof.
  induction Γ; simpl; intros. admit. mydestr.
  eapply IHΓ; eauto.
  eapply pf_implies in IHΓ; eauto. with (Γ := Γ) (P := (λ Γv : env, (⟦(m{Γv}p) τ2⟧) (λ e : tm, Pe ((m{Γv}t) e)))); eauto. admit. apply IHctxRst.


Reserved Notation "Γ '⊢' e '⋮t' τ" (at level 20).
Reserved Notation "Γ '⊢' e '⋮v' τ"  (at level 20).

(** Typing *)

Definition is_arr_pty (τ: pty) :=
  match τ with
  | _ ⤑ _ => True
  | _ => False
  end.

Inductive term_type_check : listctx pty -> tm -> pty -> Prop :=
| TValue: forall Γ v τ, Γ ⊢ v ⋮v τ ->  Γ ⊢ v ⋮t τ
| TSub: forall Γ e (τ1 τ2: pty),
    Γ ⊢WF τ2 -> Γ ⊢ e ⋮t τ1 -> Γ ⊢ τ1 <⋮ τ2 -> Γ ⊢ e ⋮t τ2
| TLetE: forall Γ e_x e τ_x τ (L: aset),
    Γ ⊢WF τ ->
    Γ ⊢ e_x ⋮t τ_x ->
    (forall x, x ∉ L -> (Γ ++ [(x, τ_x)]) ⊢ (e ^t^ x) ⋮t (τ ^p^ x)) ->
     Γ ⊢ (tlete e_x e) ⋮t τ
| TAppOver: forall Γ (f v: value) e b ϕ τx τ (L: aset),
    Γ ⊢WF τ ->
    Γ ⊢ v ⋮v ⟨:b | ϕ⟩ ->
    Γ ⊢ f ⋮v ({:b | ϕ} ⤑ τx) ->
    (forall x, x ∉ L -> (Γ ++ [(x, τx ^p^ v)]) ⊢ (e ^t^ x) ⋮t (τ ^p^ x)) ->
    Γ ⊢ (tletapp f v e) ⋮t τ
| TAppUnder: forall Γ (f v: value) e b ϕ τx τ (Lv: aset) (L: aset),
    Γ ⊢WF τ ->
    (forall xv, xv ∉ Lv -> (Γ ++ [(xv, {:b | ϕ})]) ⊢ v ⋮t (mk_eq_var b xv)) ->
    Γ ⊢ f ⋮v ([:b | ϕ] ⤑ τx) ->
    (forall (xv: atom), xv ∉ Lv ->
                   forall x, x ∉ L ->
                        (Γ ++ [(xv, {:b | ϕ}); (x, τx ^p^ xv)]) ⊢ (e ^t^ x) ⋮t (τ ^p^ x)) ->
    Γ ⊢ (tletapp f v e) ⋮t τ
| TAppArr: forall Γ (f v: value) e τv τx τ (L: aset),
    Γ ⊢WF τ ->
    is_arr_pty τv ->
    Γ ⊢ v ⋮v τv ->
    Γ ⊢ f ⋮v (τv ⤑ τx) ->
    (forall x, x ∉ L -> (Γ ++ [(x, τx ^p^ v)]) ⊢ (e ^t^ x) ⋮t (τ ^p^ x)) ->
    Γ ⊢ (tletapp f v e) ⋮t τ
with value_type_check : listctx pty -> value -> pty -> Prop :=
| TConstant: forall Γ (c: constant),
    Γ ⊢WF (mk_eq_constant c) ->
    Γ ⊢ c ⋮v (mk_eq_constant c)
| TBaseVar: forall Γ (x: atom) (b: base_ty) τ,
    Γ ⊢WF τ -> ctxfind Γ x = Some τ -> ⌊ τ ⌋ = b ->
    Γ ⊢ x ⋮v (mk_eq_var b x)
| TVar: forall Γ (x: atom) τ,
    Γ ⊢WF τ -> ctxfind Γ x = Some τ -> is_arr_pty τ ->
    Γ ⊢ x ⋮v τ
| TLam: forall Γ e Tx τ1 τ2 (L: aset),
    Γ ⊢WF (τ1 ⤑ τ2) ->
    (forall x, x ∉ L -> (Γ ++ [(x, τ1)]) ⊢ (e ^t^ x) ⋮t (τ2 ^p^ x)) ->
    Tx = ⌊ τ1 ⌋ ->
    Γ ⊢ (vlam Tx e) ⋮v (τ1 ⤑ τ2)
where
"Γ '⊢' e '⋮t' τ" := (term_type_check Γ e τ) and "Γ '⊢' e '⋮v' τ" := (value_type_check Γ e τ).

Scheme value_type_check_rec := Induction for value_type_check Sort Prop
    with term_type_check_rec := Induction for term_type_check Sort Prop.

Lemma subtyping_preserves_basic_typing Γ τ1 τ2 :
  Γ ⊢ τ1 <⋮ τ2 -> ⌊τ1⌋ = ⌊τ2⌋.
Proof.
Admitted.

Lemma value_typing_regular_wf : forall (Γ: listctx pty) (v: value) (τ: pty),
    Γ ⊢ v ⋮v τ -> closed_pty (ctxdom ⦑ Γ ⦒) τ
with tm_typing_regular_wf : forall (Γ: listctx pty) (e: tm) (τ: pty),
    Γ ⊢ e ⋮t τ -> closed_pty (ctxdom ⦑ Γ ⦒) τ.
Proof.
Admitted.


Lemma value_typing_regular_basic_typing: forall (Γ: listctx pty) (v: value) (τ: pty),
    Γ ⊢ v ⋮v τ -> ⌊ Γ ⌋* ⊢t v ⋮v ⌊ τ ⌋
with tm_typing_regular_basic_typing: forall (Γ: listctx pty) (e: tm) (τ: pty),
    Γ ⊢ e ⋮t τ -> ⌊ Γ ⌋* ⊢t e ⋮t ⌊ τ ⌋.
Proof.
Admitted.

Ltac simpl_fv :=
  do_hyps (fun H => try match type of H with
                    | _ ∉ _ =>
                        simpl in H; rewrite ?ctxRst_dom in H by eassumption
                    end).

(* At some point the proof is very slow without marking [msubst] opaque. *)
Opaque msubst.

Lemma pf_implies2 Γ (pf: prefix):
  ctxRst Γ pf -> forall (P P': env -> Prop), pf (fun (Γv: env) => closed_env Γv -> P Γv -> P' Γv) -> pf P -> pf P'.
Proof.
  induction 1; intros; eauto. apply H; eauto. admit.
  eapply IHctxRst; eauto.
  eapply pf_implies; eauto.
  intros. edestruct H6; eauto. mydestr. exists x0. split; eauto.
Admitted.

Theorem value_fundamental : forall (Γ: listctx pty) (v: value) (τ: pty),
    Γ ⊢ v ⋮v τ -> forall pf, ctxRst Γ pf -> pf (fun Γv => ⟦ msubst pty_subst Γv τ ⟧ (fun e' => e' = msubst value_subst Γv v))
with tm_fundamental : forall (Γ: listctx pty) (e: tm) (τ: pty),
    Γ ⊢ e ⋮t τ ->  forall pf, ctxRst Γ pf -> pf (fun Γv => ⟦ msubst pty_subst Γv τ ⟧ (fun e' => e' = msubst tm_subst Γv e)).
Proof.
  induction 1; intros.
  (** [TConstant] *)
  - admit.
  (** [TVarBase] *)
  - admit.
  (** [TVarArr] *)
  - admit.
  (** [TLam] *)
  - admit.
  - induction 1; intros.
    (** [TReturn] *)
    + specialize (value_fundamental _ _ _ H _ H0). eapply pf_implies; eauto. simpl. intros.
      rewrite msubst_value; auto.
    (** [TSub] *)
    + specialize (tm_fundamental _ _ _ H0 _ H2). eapply pf_implies; eauto. simpl. intros. admit.
      (* NOTE: how to define subtyping? *)
    (** [TLetE] *)
    + specialize_L. clear H1. specialize (IHterm_type_check _ H3).
      assert (ctxRst (Γ ++ [(fv_of_set L, τ_x)]) pf)

      eapply tm_fundamental in H0; eauto.

Theorem fundamental:
  well_formed_builtin_typing ->
  forall (Γ: listctx pty) (e: tm) (τ: hty),
    Γ ⊢ e ⋮t τ ->
    forall Γv, ctxRst Γ Γv -> ⟦ msubst hty_subst Γv τ ⟧ (msubst tm_subst Γv e).
Proof.
  intros HWFbuiltin.
  apply (term_type_check_rec
           (fun Γ (v: value) τ _ =>
              forall Γv, ctxRst Γ Γv -> p⟦ m{Γv}p τ ⟧ (m{Γv}v v))
           (fun Γ e (τ: hty) _ =>
              forall Γv, ctxRst Γ Γv -> ⟦ m{Γv}h τ ⟧ (m{Γv}t e))
        ).
  (* [TConstant] *)
  - intros Γ c HWF Γv HΓv. repeat msubst_simp.
    assert ((m{Γv}p) (mk_eq_constant c) = (mk_eq_constant c)) as Htmp. {
      unfold mk_eq_constant, mk_q_bvar_eq_val.
      repeat (simpl; msubst_simp).
      rewrite msubst_qualifier; eauto using ctxRst_closed_env.
      repeat (simpl; msubst_simp).
    }
    rewrite Htmp; clear Htmp.
    simpl.
    split. eauto. split. repeat econstructor.
    split. unshelve (repeat econstructor). exact ∅. simpl. repeat my_set_solver.
    intros. unfold bpropR. simpl.
    apply value_reduction_refl in H.
    simp_hyps. eauto.

  (* [TVar] *)
  - intros Γ x τ Hwf Hfind Γv HΓv. repeat msubst_simp.
    eapply ctxRst_ctxfind in HΓv; eauto.
    qauto.

  (* [TLam] *)
  - intros Γ Tx τ e T A B L HWF Ht HDe He Γv HΓv. repeat msubst_simp.
    assert (∅ ⊢t vlam Tx ((m{Γv}t) e) ⋮t Tx ⤍ T) as Hlam. {
      econstructor. econstructor.
      instantiate_atom_listctx.
      rewrite <- msubst_open_var_tm by
        (eauto using ctxRst_closed_env, ctxRst_lc; simpl_fv; my_set_solver).
      eapply msubst_preserves_basic_typing_tm; eauto.
      eapply tm_typing_regular_basic_typing in Ht.
      apply_eq Ht; eauto.
      cbn in He. subst.
      rewrite ctx_erase_app. f_equal. cbn.
      rewrite map_union_empty. eauto.
    }
    assert (closed_pty ∅ (m{Γv}p (-:τ⤑[:T|A▶B]))). {
      eapply_eq msubst_preserves_closed_pty_empty; eauto using wf_pty_closed.
    }
    destruct τ.
    + repeat msubst_simp. apply denotation_application_base_arg; eauto.
      auto_pose_fv x. repeat specialize_with x.
      intros v_x Hv_x.
      assert (ctxRst (Γ ++ [(x, {:B0|ϕ})]) (<[x := v_x]> Γv)) as HΓv'. {
        econstructor; eauto.
        econstructor; eauto using ctxRst_ok_ctx.
        sinvert HWF. sinvert H5. eauto.
        my_set_solver.
        msubst_simp.
      }
      specialize (HDe _ HΓv').
      rewrite <- msubst_intro_tm in HDe by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
      rewrite <- msubst_intro_hty in HDe by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
      repeat msubst_simp.
    + repeat msubst_simp. apply denotation_application_arr_arg; eauto.
      qauto using pty_erase_msubst_eq.
      dup_hyp HWF (fun H => apply wf_pty_arr_not_in in H; destruct H as (L'&?)).
      auto_pose_fv x. repeat specialize_with x.
      intros v_x Hv_x.
      assert (ctxRst (Γ ++ [(x, -:τ⤑[:T0|pre▶post] )]) (<[x := v_x]> Γv)) as HΓv'. {
        econstructor; eauto.
        econstructor; eauto using ctxRst_ok_ctx.
        sinvert HWF.
        apply wf_pty_closed. eauto.
        my_set_solver.
        msubst_simp.
      }
      specialize (HDe _ HΓv').
      rewrite <- msubst_intro_tm in HDe by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
      assert ((m{<[x:=v_x]> Γv}h) ([:T|A▶B] ^h^ x) = m{Γv}h [:T|A▶B]) as Htmp3. {
        rewrite <- open_not_in_eq_hty.
        apply msubst_insert_fresh_hty; eauto using ctxRst_closed_env, ptyR_closed_value.
        simpl_fv; my_set_solver.
        eauto.
      }
      rewrite Htmp3 in HDe.
      repeat msubst_simp.

  (* [TLamFix] *)
  - intros Γ Tx ϕ e T A B L HWF Hlam HDlam Γv HΓv. repeat msubst_simp.
    eapply denotation_application_fixed. {
      econstructor. econstructor.
      instantiate_atom_listctx.
      eapply value_typing_regular_basic_typing in Hlam.
      eapply_eq msubst_preserves_basic_typing_value; eauto.
      apply_eq Hlam.
      rewrite ctx_erase_app. f_equal. cbn.
      rewrite map_union_empty. eauto.
      simpl. repeat msubst_simp.
      rewrite <- msubst_open_var_tm; eauto using ctxRst_closed_env, ctxRst_lc.
      simpl_fv; my_set_solver.
    } {
      eapply_eq msubst_preserves_closed_pty_empty; eauto using wf_pty_closed.
      repeat msubst_simp.
    }
    auto_pose_fv x. repeat specialize_with x.
    intros v_x Hv_x.
    assert (ctxRst (Γ ++ [(x, {:Tx|ϕ})]) (<[x := v_x]> Γv)) as HΓv'. {
      econstructor; eauto.
      econstructor; eauto using ctxRst_ok_ctx.
      sinvert HWF. sinvert H4. eauto.
      my_set_solver.
      msubst_simp.
    }
    specialize (HDlam _ HΓv').
    simpl in HDlam.
    repeat msubst_simp.
    assert ((m{<[x:=v_x]> Γv}q) b0:x≺ x = b0:v≺ v_x) as Hq. {
      change (b0:x≺ x) with ({1 ~q> x}(b0≺b1)).
      rewrite <- msubst_intro_qualifier by
          (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
      rewrite msubst_fresh_qualifier. reflexivity.
      my_set_solver.
    }
    rewrite Hq in HDlam.
    rewrite <- msubst_intro_tm in HDlam by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
    rewrite <- msubst_intro_am in HDlam by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
    rewrite <- msubst_intro_postam in HDlam by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
    rewrite msubst_insert_fresh_qualifier in HDlam by
        (eauto using ctxRst_closed_env, ptyR_closed_value;
         simpl_fv; my_set_solver).
    rewrite msubst_insert_fresh_am in HDlam by
        (eauto using ctxRst_closed_env, ptyR_closed_value;
         simpl_fv; my_set_solver).
    rewrite msubst_insert_fresh_postam in HDlam by
        (eauto using ctxRst_closed_env, ptyR_closed_value;
         simpl_fv; my_set_solver).
    eauto.

  (* [TValue] *)
  - intros Γ v τ _ HDv Γv HΓv. specialize (HDv _ HΓv).
    repeat msubst_simp. rewrite <- denotation_value_pure. auto.

  (* [TSub] *)
  - intros Γ e τ1 τ2 HWFτ2 _ HDτ1 Hsub Γv HΓv. specialize (HDτ1 _ HΓv).
    apply Hsub in HDτ1; auto.

  (* [TLetE] *)
  - intros Γ e_x e Tx A T Bx_τx BxB_τ Bx_τx_B_τ L HWFBτ HTe_x HDe_x Hin1 Hin2 Ht He Γv HΓv.
    split; [| split]. {
      eapply msubst_preserves_basic_typing_tm_empty; eauto.
      econstructor. eauto using tm_typing_regular_basic_typing.
      instantiate_atom_listctx.
      sinvert HWFBτ.
      simpl_Forall2.
      eapply tm_typing_regular_basic_typing in Ht; eauto.
      apply_eq Ht.
      cbn. rewrite ctx_erase_app_r by my_set_solver.
      repeat f_equal. apply tm_typing_regular_wf in HTe_x.
      sinvert HTe_x. eauto.
      cbn. by rewrite <- hty_erase_msubst_eq.
    } {
      eauto using msubst_preserves_closed_hty_empty, wf_hty_closed.
    }
    repeat msubst_simp.
    intros HBtyped v HDHstepv.
    apply reduction_tlete in Hstepv. destruct Hstepv as (&  & v_x & Htmp & Hstepv_x & Hstepv).
    auto_pose_fv x. repeat specialize_with x.
    specialize (HDe_x _ HΓv). repeat msubst_simp.
    destruct HDe_x as (Hte_x & Hclosede_x & HDe_x).
    assert (amlist_typed ((m{Γv}pa) Bx_τx) Tx) as HH1. {
      clear - Hclosede_x.
      sinvert Hclosede_x. sinvert H. eauto.
    }
    specialize (HDe_x HH1 _ _ _ HDHstepv_x).
    destruct HDe_x as (Bxi' & τxi' & HinBx_τx & H& Hv_x).
    apply postam_msubst_in in HinBx_τx; eauto using ctxRst_closed_env.
    destruct HinBx_τx as (Bxi & τxi & Htmp0 & Htmp1 & HinBx_τx). subst.
    rewrite msubst_intro_tm with (x:=x) in Hstepv by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).

    assert (exists Bi τi, In (Bxi, τxi, Bi, τi) Bx_τx_B_τ) as Hin. {
      simpl_Forall2.
      eauto.
    }
    destruct Hin as (Bi & τi & Hin). clear Hin1.
    assert (In ((aconcat Bxi Bi), τi) BxB_τ) as Hinii. {
      simpl_Forall2.
      eauto.
    } clear Hin2.
    assert (ctxRst (Γ ++ [(x, τxi)]) (<[x:=v_x]> Γv)) as HH2. {
      constructor; auto.
      econstructor. eauto using ctxRst_ok_ctx. 2: my_set_solver.
      eapply tm_typing_regular_wf in HTe_x.
      sinvert HTe_x.
      qauto using wf_pty_closed.
    }
    specialize (He _ _ _ _ Hin _ HH2). repeat msubst_simp.
    destruct He as (Hte & Hclosede & He).
    assert (amlist_typed ((m{<[x:=v_x]> Γv}pa) [(Bi, τi)]) T) as HH3. {
      apply msubst_amlist_typed.
      clear - HWFBτ Hinii.
      sinvert HWFBτ.
      hnf in *.
      qauto.
    }
    specialize (He HH3 (++ βx)  v).
    assert ((a⟦(m{<[x:=v_x]> Γv}a) (aconcat A Bxi)⟧) (++ βx)) as Hconcat.
    { apply am_denotation_fv;
        eauto using ctxRst_closed_env, ptyR_closed_value.
      simpl_fv; my_set_solver.
      repeat msubst_simp. apply am_concat; auto. } repeat msubst_simp.
    specialize (He Hconcat Hstepv). destruct He as (Bi'' & τi'' & Hini & H & Hv).
    apply postam_msubst_in in Hini; eauto using ctxRst_closed_env.
    destruct Hini as (Bi' & τi' & Htmp0 & Htmp1 & Hini); subst.
    apply in_singleton in Hini. mydestr; subst.
    exists (m{<[x:=v_x]> Γv}a (aconcat Bxi Bi)), (m{<[x:=v_x]> Γv}p τi).
    repeat split. 3: auto.
    + eapply_eq postam_in_msubst. eauto using ctxRst_closed_env. eauto.
      apply msubst_insert_fresh_postam; eauto using ctxRst_closed_env, ptyR_closed_value.
      simpl_fv; my_set_solver.
    + repeat msubst_simp.
      apply am_concat; auto.
      apply am_denotation_fv; eauto using ctxRst_closed_env, ptyR_closed_value.
      simpl_fv; my_set_solver.

  (* [TApp] *)
  - intros Γ v1 v2 e τ Tx A T Bx_τx BxB_τ Bx_τx_B_τ L HWF Hv2 HDv2 Hv1 HDv1 Hin1 Hin2 Ht He Γv HΓv.
    specialize (HDv1 _ HΓv). specialize (HDv2 _ HΓv).
    split; [| split]. {
      eapply msubst_preserves_basic_typing_tm_empty; eauto.
      econstructor.
      apply_eq value_typing_regular_basic_typing; eauto.
      apply_eq value_typing_regular_basic_typing; eauto.
      instantiate_atom_listctx.
      sinvert HWF.
      simpl_Forall2.
      eapply tm_typing_regular_basic_typing in Ht; eauto.
      apply_eq Ht.
      rewrite ctx_erase_app_r by my_set_solver.
      repeat f_equal. apply value_typing_regular_wf in Hv1.
      sinvert Hv1. rewrite <- pty_erase_open_eq. eauto.
      cbn. by rewrite <- hty_erase_msubst_eq.
    } {
      eauto using msubst_preserves_closed_hty_empty, wf_hty_closed.
    }
    repeat msubst_simp.
    intros HBtyped v HDHstepv.
    apply reduction_tletapp in Hstepv. destruct Hstepv as (&  & v_x & Htmp & Hstepv_x & Hstepv).
    destruct HDv1 as (Hev1 & Htv1 & Hclosedv1 & HDv1).
    assert (amlist_typed ((m{Γv}pa) Bx_τx) Tx) as HH1. {
      clear - Hclosedv1.
      sinvert Hclosedv1. sinvert H. eauto.
    }
    case_split.
    + assert (exists c : constant, (m{Γv}v) v2 = c) as Hc. {
        sinvert HDv2.
        eapply empty_basic_typing_base_const_exists.
        simp_hyps.
        sinvert H0. eauto.
      } destruct Hc as (c & Hev2).
      rewrite msubst_open_am in HDby eauto using ctxRst_closed_env, ctxRst_lc.
      rewrite Hev2 in *.
      specialize (HDv1 HH1 _ HDv2 _ _ _ HDHstepv_x).
      destruct HDv1 as (Bxi' & τxi' & HinBx_τx & H& Hv_x).
      apply postam_msubst_in in HinBx_τx; eauto using ctxRst_closed_env.
      destruct HinBx_τx as (Bxi & τxi & Htmp0 & Htmp1 & HinBx_τx). subst.
      auto_pose_fv x. repeat specialize_with x.
      rewrite msubst_intro_tm with (x:=x) in Hstepv by
          (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
           simpl_fv; my_set_solver).
      assert (exists Bi τi, In (Bxi, τxi, Bi, τi) Bx_τx_B_τ) as Hin. {
        simpl_Forall2.
        eauto.
      }
      destruct Hin as (Bi & τi & Hin). clear Hin1.
      assert (In ((aconcat (Bxi ^a^ v2) Bi), τi) BxB_τ) as Hinii. {
        simpl_Forall2.
        eauto.
      } clear Hin2.
      assert (ctxRst (Γ ++ [(x, τxi ^p^ v2)]) (<[x:=v_x]> Γv)) as HH2. {
        constructor; auto.
        econstructor. eauto using ctxRst_ok_ctx. 2: my_set_solver.

        clear - HΓv HinBx_τx Hv1 Hv2 Hev2.
        assert (lc v2) as Hlc. {
          eauto using value_typing_regular_basic_typing, basic_typing_regular_tm.
        }
        eapply value_typing_regular_wf in Hv1.
        sinvert Hv1.
        auto_pose_fv x. repeat specialize_with x.
        eapply H8 in HinBx_τx.
        eapply wf_pty_closed in HinBx_τx.
        rewrite <- subst_intro_pty with (x:=x) by (eauto; my_set_solver).
        eapply subst_preserves_closed_pty; eauto.
        eapply msubst_constant_remove_arr_pty_ctx; eauto.

        rewrite <- Hev2 in *.
        rewrite <- msubst_open_pty in * by eauto using ctxRst_closed_env, ctxRst_lc.
        apply_eq Hv_x.
        apply ptyR_typed_closed in Hv_x.
        qauto.
      }
      specialize (He _ _ _ _ Hin _ HH2). repeat msubst_simp.
      destruct He as (Hte & Hclosede & He).
      assert (amlist_typed ((m{<[x:=v_x]> Γv}pa) [(Bi, τi)]) T) as HH3. {
        apply msubst_amlist_typed.
        clear - HWF Hinii.
        sinvert HWF.
        hnf in *.
        qauto.
      }
      specialize (He HH3 (++ βx)  v).
      rewrite <- Hev2 in *.
      rewrite <- msubst_open_am in * by eauto using ctxRst_closed_env, ctxRst_lc.
      assert ((a⟦(m{<[x:=v_x]> Γv}a) (aconcat (A ^a^ v2) (Bxi ^a^ v2))⟧) (++ βx)) as Hconcat.
      { apply am_denotation_fv;
          eauto using ctxRst_closed_env, ptyR_closed_value.
        simpl_fv; my_set_solver.
        repeat msubst_simp.
        apply am_concat; auto.
      } repeat msubst_simp.
      specialize (He Hconcat Hstepv). destruct He as (Bi'' & τi'' & Hini & H & Hv).
      apply postam_msubst_in in Hini; eauto using ctxRst_closed_env.
      destruct Hini as (Bi' & τi' & Htmp0 & Htmp1 & Hini); subst.
      apply in_singleton in Hini. mydestr; subst.
      exists (m{<[x:=v_x]> Γv}a (aconcat (Bxi ^a^ v2) Bi)), (m{<[x:=v_x]> Γv}p τi).
      repeat split. 3: auto.
      * eapply_eq postam_in_msubst. eauto using ctxRst_closed_env. eauto.
        apply msubst_insert_fresh_postam; eauto using ctxRst_closed_env, ptyR_closed_value.
        simpl_fv; my_set_solver.
      * repeat msubst_simp.
        apply am_concat; auto.
        apply am_denotation_fv; eauto using ctxRst_closed_env, ptyR_closed_value.
        simpl_fv; my_set_solver.
    + pose proof Hv1 as HWFv1.
      apply value_typing_regular_wf in HWFv1.
      destruct τ; msubst_simp. simplify_eq.
      dup_hyp HWFv1 (fun H => apply wf_pty_arr_not_in in H; destruct H as (L'&?)).
      auto_pose_fv x. repeat specialize_with x.
      rewrite <- (open_not_in_eq_am x) in * by my_set_solver.
      specialize (HDv1 HH1 _ HDv2 _ _ _ HDHstepv_x).
      destruct HDv1 as (Bxi' & τxi' & HinBx_τx & H& Hv_x).
      apply postam_msubst_in in HinBx_τx; eauto using ctxRst_closed_env.
      destruct HinBx_τx as (Bxi & τxi & Htmp0 & Htmp1 & HinBx_τx). subst.
      rewrite msubst_intro_tm with (x:=x) in Hstepv by
          (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
           simpl_fv; my_set_solver).
      assert (exists Bi τi, In (Bxi, τxi, Bi, τi) Bx_τx_B_τ) as Hin. {
        simpl_Forall2.
        eauto.
      }
      destruct Hin as (Bi & τi & Hin). clear Hin1.
      assert (x ∉ stale (Bxi ^a^ x) ∪ stale (τxi ^p^ x)) as Hfresh. {
        simpl in H. rewrite not_elem_of_union in H. destruct H as (_ & H).
        eapply postam_in_open in HinBx_τx.
        eapply not_in_union_list in H; cycle 1.
        rewrite in_map_iff. eauto.
        my_set_solver.
      }
      assert (In ((aconcat Bxi Bi), τi) BxB_τ) as Hinii. {
        simpl_Forall2.
        rewrite <- (open_not_in_eq_am x) in * by my_set_solver.
        eauto.
      } clear Hin2.
      assert (ctxRst (Γ ++ [(x, τxi)]) (<[x:=v_x]> Γv)) as HH2. {
        constructor; auto.
        econstructor. eauto using ctxRst_ok_ctx. 2: my_set_solver.

        clear - HWFv1 Hfresh HinBx_τx.
        sinvert HWFv1.
        auto_pose_fv x'. repeat specialize_with x'.
        eapply H8 in HinBx_τx.
        rewrite <- (open_not_in_eq_pty x) in HinBx_τx by my_set_solver.
        apply wf_pty_closed in HinBx_τx.
        apply_eq HinBx_τx.
        rewrite remove_arr_pty_ctx_dom_union.
        simpl. my_set_solver.

        apply_eq Hv_x.
        apply ptyR_typed_closed in Hv_x. intuition.
      }
      specialize (He _ _ _ _ Hin).
      rewrite <- (open_not_in_eq_pty x) in He by my_set_solver.
      rewrite <- (open_not_in_eq_am x) in He by my_set_solver.
      specialize (He _ HH2). repeat msubst_simp.
      destruct He as (Hte & Hclosede & He).
      assert (amlist_typed ((m{<[x:=v_x]> Γv}pa) [(Bi, τi)]) T) as HH3. {
        apply msubst_amlist_typed.
        clear - HWF Hinii.
        sinvert HWF.
        hnf in *.
        qauto.
      }
      specialize (He HH3 (++ βx)  v).
      assert ((a⟦(m{<[x:=v_x]> Γv}a) (aconcat A Bxi)⟧) (++ βx)) as Hconcat.
      { apply am_denotation_fv;
          eauto using ctxRst_closed_env, ptyR_closed_value.
        simpl_fv. my_set_solver.
        repeat msubst_simp. apply am_concat; auto. } repeat msubst_simp.
      specialize (He Hconcat Hstepv). destruct He as (Bi'' & τi'' & Hini & H & Hv).
      apply postam_msubst_in in Hini; eauto using ctxRst_closed_env.
      destruct Hini as (Bi' & τi' & Htmp0 & Htmp1 & Hini); subst.
      apply in_singleton in Hini. mydestr; subst.
      exists (m{<[x:=v_x]> Γv}a (aconcat Bxi Bi)), (m{<[x:=v_x]> Γv}p τi).
      repeat split. 3: auto.
      * eapply_eq postam_in_msubst. eauto using ctxRst_closed_env. eauto.
        apply msubst_insert_fresh_postam; eauto using ctxRst_closed_env, ptyR_closed_value.
        simpl_fv; my_set_solver.
      * repeat msubst_simp.
        apply am_concat; auto.
        apply am_denotation_fv; eauto using ctxRst_closed_env, ptyR_closed_value.
        simpl_fv; my_set_solver.

  (* [TEffOp] *)
  - intros Γ op v2 e ϕx A T Bx_τx opϕB_τ ϕ_B_τ L HWF Hv2 HDv2 HWFp Hbuiltin Hin1 Hin2 Ht He Γv HΓv.
    specialize (HDv2 _ HΓv).
    split; [| split]. {
      eapply msubst_preserves_basic_typing_tm_empty; eauto.
      econstructor.
      apply_eq value_typing_regular_basic_typing; eauto. eauto.
      instantiate_atom_listctx.
      sinvert HWF.
      simpl_Forall2.
      eapply tm_typing_regular_basic_typing in Ht; eauto.
      apply_eq Ht.
      rewrite ctx_erase_app_r by my_set_solver. eauto.
      cbn. by rewrite <- hty_erase_msubst_eq.
    } {
      eauto using msubst_preserves_closed_hty_empty, wf_hty_closed.
    }
    repeat msubst_simp.
    intros HBtyped v HDHstepv.
    apply reduction_tletprimop in Hstepv. destruct Hstepv as (c2 & c_x & β' & Htmp1 & Htmp2 & Htr & Hstepv).
    assert (amlist_typed ((m{Γv}pa) Bx_τx) (ret_ty_of_op op)) as HH1. {
      clear - HWFp.
      sinvert HWFp. eauto using msubst_amlist_typed.
    }
    rewrite msubst_open_am in HDby eauto using ctxRst_closed_env, ctxRst_lc.
    rewrite Htmp1 in *.
    hnf in HWFbuiltin.
    apply HWFbuiltin with (Γv:=Γv) in Hbuiltin; eauto.
    rename Hbuiltin into HDop.
    hnf in HDop. repeat msubst_simp.
    specialize (HDop _ HDv2 _ HD_ Htr).
    destruct HDop as (Bxi' & τxi' & HinBx_τx & HDc_x).
    apply postam_msubst_in in HinBx_τx; eauto using ctxRst_closed_env.
    destruct HinBx_τx as (Bxi & τxi & -> & -> & HinBx_τx). subst.
    auto_pose_fv x. repeat specialize_with x.
    rewrite msubst_intro_tm with (x:=x) in Hstepv by
        (eauto using ctxRst_closed_env, ctxRst_lc, ptyR_closed_value;
         simpl_fv; my_set_solver).
    assert (exists ϕ Bi τi, Bxi = aϵ /\ τxi = {:ret_ty_of_op op|ϕ} /\ In (ϕ, Bi, τi) ϕ_B_τ) as Hin. {
      simpl_Forall2.
      eauto 10.
    }
    destruct Hin as (ϕy & Bi & τi & -> & -> & Hin). clear Hin1.
    assert (In ((aconcat (⟨op| b1:v= v2 & ϕy⟩) Bi), τi) opϕB_τ) as Hinii. {
      simpl_Forall2.
      eauto.
    } clear Hin2.
    assert (ctxRst (Γ ++ [(x, {:ret_ty_of_op op|ϕy} ^p^ v2)]) (<[x:=vconst c_x]> Γv)) as HH2. {
      constructor; auto.
      econstructor. eauto using ctxRst_ok_ctx. 2: my_set_solver.
      assert (lc v2) as Hlc. {
        clear - Hv2.
        apply value_typing_regular_basic_typing in Hv2.
        apply basic_typing_regular_value in Hv2. eauto.
      }
      clear - HinBx_τx HWFp HΓv Hlc Htmp1.
      sinvert HWFp.
      auto_pose_fv x. repeat specialize_with x.
      apply H8 in HinBx_τx.
      eapply wf_pty_closed in HinBx_τx.
      eapply subst_preserves_closed_pty in HinBx_τx; eauto.
      rewrite subst_intro_pty in HinBx_τx; eauto.
      my_set_solver.
      eapply msubst_constant_remove_arr_pty_ctx; eauto.

      clear - HDc_x HΓv Htmp1.
      rewrite msubst_open_pty by eauto using ctxRst_closed_env, ctxRst_lc.
      rewrite Htmp1. eauto.
    }
    specialize (He _ _ _ Hin _ HH2). repeat msubst_simp.
    destruct He as (Hte & Hclosede & He).
    assert (amlist_typed ((m{<[x:=vconst c_x]> Γv}pa) [(Bi, τi)]) T) as HH3. {
      apply msubst_amlist_typed.
      clear - HWF Hinii.
      sinvert HWF.
      hnf in *.
      qauto.
    }
    specialize (He HH3 (++ [ev{op~c2:=c_x}]) β' v).
    feed specialize He; eauto. {
      apply am_concat; auto.
      rewrite <- Htmp1 in *.
      rewrite <- msubst_open_am in * by eauto using ctxRst_closed_env, ctxRst_lc.
      apply am_denotation_fv;
        eauto using ctxRst_closed_env, ptyR_closed_value.
      simpl_fv; my_set_solver.
      (* Should be a lemma. *)
      split.
      (* lemma? *)
      econstructor.
      sinvert Hclosede. sinvert H1.
      sinvert H6. eauto.
      sinvert Hclosede. sinvert H1.
      simpl in H2.
      rewrite !union_subseteq in H2. simp_hyps.
      eauto.

      repeat esplit; eauto.
      apply ptyR_typed_closed in HDv2. simp_hyps. sinvert H1. eauto.
      sinvert HDc_x. simp_hyps. sinvert H1. eauto.

      rewrite !qualifier_and_open.
      apply denote_qualifier_and.
      rewrite !msubst_qualifier by eauto using ctxRst_closed_env.
      cbn. repeat msubst_simp.
      cbn. rewrite !decide_True by auto.
      cbn. rewrite !decide_False by auto.
      cbn. rewrite !decide_True by auto.
      rewrite_msubst_insert; eauto using ctxRst_closed_env, ptyR_closed_value.
      2: apply not_elem_of_dom; simpl_fv; my_set_solver.
      rewrite Htmp1. cbn. rewrite lookup_insert. cbn. intuition.
    }
    repeat msubst_simp.
    destruct He as (Bi'' & τi'' & Hini & H & Hv).
    apply postam_msubst_in in Hini; eauto using ctxRst_closed_env.
    destruct Hini as (Bi' & τi' & -> & -> & Hini); subst.
    apply in_singleton in Hini. mydestr; subst.
    exists (m{<[x:=vconst c_x]> Γv}a (aconcat (⟨op|b1:v= v2 & ϕy⟩) Bi)), (m{<[x:=vconst c_x]> Γv}p τi).
    repeat split. 3: auto.
    + eapply_eq postam_in_msubst. eauto using ctxRst_closed_env. eauto.
      apply msubst_insert_fresh_postam; eauto using ctxRst_closed_env, ptyR_closed_value.
      simpl_fv; my_set_solver.
    + repeat msubst_simp.
      rewrite <- app_one_is_cons.
      apply am_concat; auto.
      apply am_denotation_fv; eauto using ctxRst_closed_env, ptyR_closed_value.
      simpl_fv; my_set_solver.
      (* should be a lemma *)
      rewrite msubst_aevent; eauto using ctxRst_closed_env.
      cbn. cbn in HDc_x. simp_hyps.
      sinvert H0.
      sinvert H1.
      repeat msubst_simp.
      rewrite msubst_qualifier by eauto using ctxRst_closed_env. simpl.
      repeat msubst_simp. rewrite Htmp1.
      split.

      econstructor; eauto.
      clear - H5.
      sinvert H5.
      econstructor.
      instantiate_atom_listctx.
      rewrite !qualifier_and_open.
      apply lc_qualifier_and.
      cbn. rewrite decide_True by auto. cbn. repeat econstructor.
      rewrite open_swap_qualifier in *; eauto using lc.
      eauto using open_lc_respect_qualifier.

      simpl. rewrite qualifier_and_fv. simpl.
      simpl in H6. rewrite <- open_fv_qualifier' in H6.
      clear - H6.
      repeat my_set_solver.

      repeat esplit; eauto.
      apply ptyR_typed_closed in HDv2. simp_hyps. sinvert H1. eauto.
      rewrite !qualifier_and_open.
      apply denote_qualifier_and.
      split.
      cbn. cbn. rewrite decide_True by auto. cbn. eauto.
      eapply (H2 _ [] []). repeat econstructor.

  (* [TMatchb] *)
  - intros Γ v e1 e2 ϕ τ L HWFτ Htv HDv Hte1 HDe1 Hte2 HDe2 Γv HΓv.
    specialize (HDv _ HΓv).
    auto_pose_fv x. repeat specialize_with x.
    split; [| split]. {
      eapply msubst_preserves_basic_typing_tm_empty; eauto.
      econstructor.
      qauto using value_typing_regular_basic_typing.
      rewrite <- hty_erase_msubst_eq.
      eapply tm_typing_regular_basic_typing in Hte1.
      eapply basic_typing_strengthen_tm.
      rewrite <- ctx_erase_app_r.
      eauto. my_set_solver. my_set_solver.
      rewrite <- hty_erase_msubst_eq.
      eapply tm_typing_regular_basic_typing in Hte2.
      eapply basic_typing_strengthen_tm.
      rewrite <- ctx_erase_app_r.
      eauto. my_set_solver. my_set_solver.
    } {
      eauto using msubst_preserves_closed_hty_empty, wf_hty_closed.
    }
    destruct τ. repeat msubst_simp.
    intros HBtyped v' HDHstepv.
    assert ((m{Γv}v) v = true \/ (m{Γv}v) v = false) as Hv. {
      apply value_typing_regular_basic_typing in Htv.
      eapply msubst_preserves_basic_typing_value_empty in Htv; eauto.
      eapply empty_basic_typing_bool_value_exists in Htv.
      eauto.
    }
    destruct Hv as [Hv | Hv]; rewrite Hv in *.
    + apply reduction_matchb_true in Hstepv; mydestr; auto.
      assert (closed_pty (ctxdom ⦑Γ⦒) {:TBool|(b0:c=true) & ((b0:v=v) & ϕ)}) as Hc. {
        assert (lc v) as Hlc by
          eauto using value_typing_regular_basic_typing, basic_typing_regular_value.
        clear - Htv Hlc Hv HΓv.
        eapply value_typing_regular_wf in Htv.
        sinvert Htv. sinvert H1.
        econstructor. econstructor.
        sinvert H0.
        econstructor.
        intros. rewrite !qualifier_and_open.
        repeat apply lc_qualifier_and; eauto.
        repeat econstructor.
        repeat econstructor. by rewrite open_rec_lc_value.
        simpl. rewrite !qualifier_and_fv. simpl.
        eapply msubst_constant_remove_arr_pty_ctx in Hv; eauto.
        repeat my_set_solver.
      }
      assert (ctxRst (Γ ++ [(x, {:TBool|(b0:c=true) & ((b0:v=v) & ϕ)})]) (<[x:=vconst true]> Γv)) as HΓv'. {
        constructor; auto.
        econstructor. eauto using ctxRst_ok_ctx. 2: my_set_solver.
        eauto.

        clear - Hv HDv HΓv Hc.
        eapply msubst_preserves_closed_pty_empty in Hc; eauto.
        repeat msubst_simp.
        simpl in HDv.
        simpl.
        simp_hyps.
        repeat (split; eauto).
        unfold bpropR in *.
        specialize (H2 _ _ _ H3).
        apply value_reduction_refl in H3. simp_hyps. subst.
        rewrite !qualifier_and_open.
        rewrite !denote_qualifier_and. repeat split; eauto.
        rewrite msubst_qualifier by eauto using ctxRst_closed_env. simpl.
        repeat msubst_simp. cbn. rewrite decide_True by auto. eauto.
        rewrite msubst_qualifier by eauto using ctxRst_closed_env. simpl.
        repeat msubst_simp. cbn. rewrite decide_True by auto.
        rewrite Hv. cbn. eauto.
      }
      specialize (HDe1 _ HΓv').
      msubst_simp.
      destruct HDe1 as (HTe1 & Hclosede1 & HDe1).
      rewrite msubst_insert_fresh_postam,
        msubst_insert_fresh_am,
        msubst_insert_fresh_tm in HDe1;
        eauto using ctxRst_closed_env; simpl_fv; my_set_solver.
    + apply reduction_matchb_false in Hstepv; mydestr; auto.
      assert (closed_pty (ctxdom ⦑Γ⦒) {:TBool|(b0:c=false) & ((b0:v=v) & ϕ)}) as Hc. {
        assert (lc v) as Hlc by
          eauto using value_typing_regular_basic_typing, basic_typing_regular_value.
        clear - Htv Hlc Hv HΓv.
        eapply value_typing_regular_wf in Htv.
        sinvert Htv. sinvert H1.
        econstructor. econstructor.
        sinvert H0.
        econstructor.
        intros. rewrite !qualifier_and_open.
        repeat apply lc_qualifier_and; eauto.
        repeat econstructor.
        repeat econstructor. by rewrite open_rec_lc_value.
        simpl. rewrite !qualifier_and_fv. simpl.
        eapply msubst_constant_remove_arr_pty_ctx in Hv; eauto.
        repeat my_set_solver.
      }
      assert (ctxRst (Γ ++ [(x, {:TBool|(b0:c=false) & ((b0:v=v) & ϕ)})]) (<[x:=vconst false]> Γv)) as HΓv'. {
        constructor; auto.
        econstructor. eauto using ctxRst_ok_ctx. 2: my_set_solver.
        eauto.

        clear - Hv HDv HΓv Hc.
        eapply msubst_preserves_closed_pty_empty in Hc; eauto.
        repeat msubst_simp.
        simpl in HDv.
        simpl.
        simp_hyps.
        repeat (split; eauto).
        intros.
        unfold bpropR in *.
        specialize (H2 _ _ _ H3).
        apply value_reduction_refl in H3. simp_hyps. subst.
        rewrite !qualifier_and_open.
        rewrite !denote_qualifier_and. repeat split; eauto.
        rewrite msubst_qualifier by eauto using ctxRst_closed_env. simpl.
        repeat msubst_simp. cbn. rewrite decide_True by auto. eauto.
        rewrite msubst_qualifier by eauto using ctxRst_closed_env. simpl.
        repeat msubst_simp. cbn. rewrite decide_True by auto.
        rewrite Hv. cbn. eauto.
      }
      specialize (HDe2 _ HΓv').
      msubst_simp.
      destruct HDe2 as (HTe2 & Hclosede2 & HDe2).
      rewrite msubst_insert_fresh_postam,
        msubst_insert_fresh_am,
        msubst_insert_fresh_tm in HDe2;
        eauto using ctxRst_closed_env; simpl_fv; my_set_solver.
Qed.

Transparent msubst.

Definition valid_evop '(evop_ op argv retv) :=
  ∅ ⊢t argv ⋮v TNat /\ ∅ ⊢t retv ⋮v ret_ty_of_op op.

Definition valid_trace := Forall valid_evop.

Lemma valid_evop_any ev :
  valid_evop ev ->
  a⟦ ∘ ⟧ [ev].
Proof.
  intros H. split. repeat econstructor. my_set_solver.
  destruct ev. repeat esplit; qauto.
Qed.

Lemma valid_trace_any_star :
  valid_trace ->
  a⟦ astar ∘ ⟧ α.
Proof.
  intros H.
  split. repeat econstructor. my_set_solver.
  induction α. constructor.
  rewrite <- app_one_is_cons.
  sinvert H.
  econstructor; eauto using valid_evop_any.
Qed.

Corollary soundness :
  well_formed_builtin_typing ->
  forall (e : tm) T B,
    [] ⊢ e ⋮t [: T | astar ∘ ▶ B] ->
    forall (v : value),
      (* Alternatively, we can simply say [a⟦ astar ∘ ⟧ α]. *)
      valid_trace ->
      e ↪* v ->
      exists Bi τi, In (Bi, τi) B /\
                 a⟦ Bi ⟧ /\
                 p⟦ τi ⟧ v.
Proof.
  intros HWFbuiltin **.
  apply fundamental with (Γv := ∅) in H; eauto using ctxRst.
  unfold msubst in *.
  rewrite !map_fold_empty in *.
  destruct H as (Ht & Hc & H).
  eapply H; eauto.
  sinvert Hc. sinvert H2. eauto.
  eauto using valid_trace_any_star.
Qed.

Print Assumptions soundness.
