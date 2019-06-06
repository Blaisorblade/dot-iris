From iris.proofmode Require Import tactics.
From D.DSub Require Export unary_lr synLemmas.
Import uPred.

Implicit Types
         (L T U: ty) (v: vl) (e: tm)
         (Γ : ctx) (ρ : vls).

(* Lemmas about the logical relation itself. *)
Section logrel_binding_lemmas.
  Context `{!dlangG Σ}.

  Lemma interp_weaken ρ1 ρ2 ρ3 τ :
    ⟦ τ.|[upn (length ρ1) (ren (+ length ρ2))] ⟧ (ρ1 ++ ρ2 ++ ρ3)
    ≡ ⟦ τ ⟧ (ρ1 ++ ρ3).
  Proof.
    revert ρ1 ρ2 ρ3; induction τ=> ρ1 ρ2 ρ3 w /=; properness; try solve [
      trivial | apply IHτ | apply IHτ1 | apply IHτ2 | apply (IHτ2 (_ :: _)) | apply (IHτ (_ :: _)) |
      asimpl; rewrite ?to_subst_weaken //].
  Qed.

  Lemma interp_weaken_one v τ ρ:
     ⟦ τ.|[ren (+1)] ⟧ (v :: ρ) ≡ ⟦ τ ⟧ ρ.
  Proof. apply (interp_weaken [] [v]). Qed.

  Lemma interp_subst_up ρ1 ρ2 τ v:
    ⟦ τ.|[upn (length ρ1) (v.[ren (+length ρ2)] .: ids)] ⟧ (ρ1 ++ ρ2)
    ≡ ⟦ τ ⟧ (ρ1 ++ v :: ρ2).
  Proof.
    revert ρ1 ρ2; induction τ=> ρ1 ρ2 w /=; properness; try solve [
      trivial | apply IHτ | apply IHτ1 | apply IHτ2 | apply (IHτ2 (_ :: _)) | apply (IHτ (_ :: _)) |
      asimpl; rewrite ?to_subst_up //].
  Qed.

  Lemma interp_subst ρ τ v1 v2 : ⟦ τ.|[v1.[ren (+length ρ)]/] ⟧ ρ v2 ≡ ⟦ τ ⟧ (v1 :: ρ) v2.
  Proof. apply (interp_subst_up []). Qed.

  Context Γ.

  Lemma interp_env_ρ_fv ρ: ⟦ Γ ⟧* ρ -∗ ⌜ nclosed ρ 0 ⌝.
  Proof.
    rewrite interp_env_ρ_closed. iPureIntro. exact: cl_ρ_fv.
  Qed.

  Lemma interp_env_to_subst_closed ρ x: x < length ρ → ⟦ Γ ⟧* ρ -∗ ⌜ nclosed_vl (to_subst ρ x) 0 ⌝%I.
  Proof.
    rewrite interp_env_ρ_closed. iPureIntro => ??. exact: closed_to_subst.
  Qed.

  Lemma interp_env_lookup ρ T x:
    Γ !! x = Some T →
    ⟦ Γ ⟧* ρ -∗ ⟦ T.|[ren (+x)] ⟧ ρ (to_subst ρ x).
  Proof.
    iIntros (Hx) "* Hg".
    iInduction Γ as [|T' Γ'] "IHL" forall (x ρ Hx); simpl; first solve [inversion Hx].
    destruct ρ; first by [iExFalso]; rewrite to_subst_cons.
    case: x Hx => /= [|x] Hx.
    - move: Hx => [ -> ]. iClear "IHL". locAsimpl.
      by iDestruct "Hg" as "[_ $]".
    - iAssert (⟦ T.|[ren (+x)] ⟧ ρ (to_subst ρ x)) with "[Hg]" as "Hv".
      by iDestruct "Hg" as "[Hg _]"; iApply "IHL".
      iClear "IHL".
      iDestruct (interp_weaken_one v with "Hv") as "Hv".
      by iEval (locAsimpl) in "Hv".
  Qed.

  Lemma interp_subst_all ρ τ v:
    cl_ρ ρ → ⟦ τ.|[to_subst ρ] ⟧ [] v ≡ ⟦ τ ⟧ ρ v.
  Proof.
    elim: ρ τ => /= [|w ρ IHρ] τ Hwρcl /=.  by rewrite to_subst_nil hsubst_id.
    assert (nclosed_vl w 0 /\ Forall (λ v, nclosed_vl v 0) ρ) as [Hwcl Hρcl]. by inversion Hwρcl.
    specialize (IHρ (τ.|[w/]) Hρcl).
    asimpl in IHρ. move: IHρ.
    by rewrite -interp_subst !closed_subst_vl_id.
  Qed.

  Lemma to_subst_interp T ρ v w: cl_ρ ρ → nclosed_vl v (length ρ) →
    ⟦ T.|[v/] ⟧ ρ w ≡ ⟦ T.|[v.[to_subst ρ]/] ⟧ ρ w.
  Proof.
    intros Hclρ Hclv.
    rewrite -(interp_subst_all ρ (T.|[v/])) // -(interp_subst_all ρ (T.|[v.[to_subst ρ]/])) //; f_equiv.
    asimpl.
    have ->: (v.[to_subst ρ] = v.[to_subst ρ >> to_subst ρ]); last done.
    apply Hclv => x Hl.
    asimpl.
    rewrite closed_subst_vl_id //. by apply closed_to_subst.
  Qed.

  Lemma ietp_closed_vl T v: (Γ ⊨ tv v : T → ⌜ nclosed_vl v (length Γ) ⌝)%I.
  Proof. rewrite ietp_closed; iPureIntro; exact: fv_tv_inv. Qed.

  Lemma interp_subst_internal ρ τ v1 v2 : (⟦ τ.|[v1.[ren (+length ρ)]/] ⟧ ρ v2 ≡ ⟦ τ ⟧ (v1 :: ρ) v2)%I : iProp Σ.
  Proof. rewrite (interp_subst ρ τ v1 v2). apply internal_eq_refl. Qed.

  Lemma interp_subst_closed T v w ρ:
    nclosed_vl v (length Γ) →
    ⟦ Γ ⟧* ρ -∗ ⟦ T.|[v/] ⟧ ρ w ≡ ⟦ T ⟧ (v.[to_subst ρ] :: ρ) w.
  Proof.
    iIntros (Hcl) "Hg".
    iDestruct (interp_env_props with "Hg") as %[Hclp Hlen]; rewrite <- Hlen in *.
    iRewrite -(interp_subst_internal ρ T (v.[to_subst ρ]) w). asimpl.
    rewrite (Hcl (to_subst ρ >> ren (+length ρ)) (to_subst ρ))
      -?(to_subst_interp T ρ v w) // => x Hlρ.
    asimpl. by rewrite closed_subst_vl_id; [|apply closed_to_subst].
  Qed.

  Lemma interp_subst_commute T σ ρ v:
    nclosed T (length σ) →
    nclosed_σ σ (length ρ) →
    cl_ρ ρ →
    ⟦ T.|[to_subst σ] ⟧ ρ v ≡ ⟦ T ⟧ σ.|[to_subst ρ] v.
  Proof.
    intros HclT Hclσ Hclρ.
    rewrite -(interp_subst_all ρ _ v) // -(interp_subst_all _ T v).
    - by erewrite subst_compose.
    - by apply nclosed_σ_to_subst.
  Qed.
End logrel_binding_lemmas.
