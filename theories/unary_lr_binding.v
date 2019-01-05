From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import tactics.
From Dot Require Export unary_lr synLemmas.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms)
         (Γ : ctx) (ρ : leibnizC vls).

(* Lemmas about the logical relation itself. *)
Section logrel_binding_lemmas.
  Context `{HdotG: dotG Σ}.

  Lemma def_interp_v_closed T d l ρ: (def_interp T l ρ d → ⌜ nclosed d 0 ⌝)%I.
  Proof.
    iInduction T as [] "IH" forall (ρ d); iIntros "#HT //="; by iDestruct "HT" as "[% [% _]]".
  Qed.

  Lemma defs_interp_v_closed T ds ρ: (defs_interp T ρ ds → ⌜ nclosed ds 0 ⌝)%I.
  Proof.
    iInduction T as [] "IH" forall (ρ ds); iIntros "#HT //=".
    destruct ds. done.
    iDestruct "HT" as "[HT1 HT2]".
    iPoseProof ("IH" with "HT1") as "%".
    iPoseProof (def_interp_v_closed with "HT2") as "%".
    iPureIntro. by apply fv_dms_cons.
  Qed.

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

  Lemma interp_env_lookup ρ T x:
    Γ !! x = Some T →
    (⟦ Γ ⟧* ρ → ⟦ T.|[ren (+x)] ⟧ ρ (to_subst ρ x))%I.
  Proof.
    iIntros (Hx) "* #Hg".
    iInduction Γ as [|T' Γ'] "IHL" forall (x ρ Hx); simpl; try solve [inversion Hx].
    destruct ρ; try by iExFalso.
    iDestruct "Hg" as "[̋Hg Ht]".
    case: x Hx => /= [|x] Hx.
    - move: Hx => [ -> ]. iSpecialize ("IHL" $! 0). by asimpl.
    - rewrite to_subst_cons /=.
      iAssert (⟦ T.|[ren (+x)] ⟧ ρ (to_subst ρ x)) as "#Hv". by iApply "IHL".
      iPoseProof (interp_weaken [] [v] ρ with "Hv") as "H"; asimpl. iExact "H".
  Qed.

  Lemma interp_subst_all ρ τ v:
    cl_ρ ρ → ⟦ τ.|[to_subst ρ] ⟧ [] v ≡ ⟦ τ ⟧ ρ v.
  Proof.
    elim: ρ τ => /= [|w ρ IHρ] τ Hwρcl; asimpl; first by [].
    assert (nclosed_vl w 0 /\ Forall (λ v, nclosed_vl v 0) ρ) as [Hwcl Hρcl]. by inversion Hwρcl.
    specialize (IHρ (τ.|[w/]) Hρcl).
    asimpl in IHρ. move: IHρ. rewrite closed_subst_vl_id// => IHρ.
    rewrite IHρ -interp_subst closed_subst_vl_id //.
  Qed.

  Lemma to_subst_interp T ρ v w: cl_ρ ρ → nclosed_vl v (length ρ) →
    ⟦ T.|[v/] ⟧ ρ w ≡ ⟦ T.|[v.[to_subst ρ]/] ⟧ ρ w.
  Proof.
    intros Hclρ Hclv.
    assert (v.[to_subst ρ] = v.[to_subst ρ >> to_subst ρ]) as Hrew. {
      apply Hclv.
      intros x Hl.
      asimpl.
      rewrite closed_subst_vl_id //. by apply closed_to_subst.
    }
    rewrite -(interp_subst_all ρ (T.|[v/])) // -(interp_subst_all ρ (T.|[v.[to_subst ρ]/])) //.
    asimpl. by rewrite -Hrew.
  Qed.

  Lemma interp_env_to_subst_closed ρ x: x < length ρ → (⟦ Γ ⟧* ρ → ⌜ nclosed_vl (to_subst ρ x) 0 ⌝)%I.
  Proof.
    iIntros (Hl) "#HG". iPoseProof (interp_env_ρ_closed with "HG") as "%".
    iPureIntro; by apply closed_to_subst.
  Qed.

  Lemma ietp_closed_vl T v: (Γ ⊨ tv v : T → ⌜ nclosed_vl v (length Γ) ⌝)%I.
  Proof.
    iIntros "H".
    iPoseProof (ietp_closed with "H") as "%". by iPureIntro; apply fv_tv_inv.
  Qed.

  (* Lemma interp_env_to_subst_closed ρ x: x < length ρ → (⟦ Γ ⟧* ρ → ⌜ nclosed_vl (to_subst ρ x) 0 ⌝)%I. *)
  (* Proof. *)
  (*   (* Hint Resolve defs_interp_v_closed def_interp_v_closed interp_v_closed. *) *)
  (*   revert Γ ρ x. *)
  (*   elim => [|T Γ IHl] [|v ρ] [|x] /= Hl; try omega; try (iIntros "%"; discriminate); iIntros "[#HG #HT]". *)
  (*   - iApply interp_v_closed. rewrite to_subst_cons /=. iApply "HT". *)
  (*   - asimpl. by iApply IHl; first omega. *)
  (* Qed. *)

  (* Lemma interp_subst_closed T v w ρ: *)
  (*   nclosed_vl v (length ρ) → *)
  (*   (⟦ Γ ⟧* ρ → ⟦ T.|[v/] ⟧ ρ w ∗-∗ ⟦ T ⟧ (v.[to_subst ρ] :: ρ) w)%I. *)
  (* Proof. *)
  (*   iIntros (Hcl) "#HG". *)
  (*   iAssert ⌜ cl_ρ ρ ⌝%I as "%". by iApply interp_env_ρ_closed. move: H => Hclρ. *)
  (*   assert (⟦ T.|[v.[to_subst ρ]/] ⟧ ρ w ≡ ⟦ T.|[v/] ⟧ ρ w) as Hren. by rewrite (to_subst_interp T ρ v w). *)
  (*   iPoseProof (interp_subst ρ T (v.[to_subst ρ]) w) as "Heq"; asimpl. *)
  (*   iAssert (⌜ eq_n_s (to_subst ρ >> ren (+length ρ)) (to_subst ρ) (length ρ) ⌝)%I as "%". *)
  (*   { *)
  (*     iIntros (x Hxl). *)
  (*     iPoseProof (interp_env_to_subst_closed ρ x Hxl with "HG") as "%". move: H => Hclx. *)
  (*     iPureIntro; apply closed_subst_vl_id, Hclx. *)
  (*   } *)
  (*   rewrite (Hcl (to_subst ρ >> ren (+length ρ)) (to_subst ρ)) //. *)
  (*   rewrite Hren. *)
  (*   iExact "Heq". *)
  (* Qed. *)

  (* Try giving a simpler proof: *)
  Lemma interp_subst_closed_aux T v w ρ:
    nclosed_vl v (length ρ) →
    (⟦ Γ ⟧* ρ → ⟦ T.|[v/] ⟧ ρ w ∗-∗ ⟦ T ⟧ (v.[to_subst ρ] :: ρ) w)%I.
  Proof.
    iIntros (Hcl) "#Hg".
    iPoseProof (interp_env_ρ_closed with "Hg") as "%"; move: H => Hclρ.
    iPoseProof (interp_subst ρ T (v.[to_subst ρ]) w) as "Heq"; iEval (asimpl) in "Heq".
    rewrite (Hcl (to_subst ρ >> ren (+length ρ)) (to_subst ρ)) // -?(to_subst_interp T ρ v w) //.
    move => x Hlρ. asimpl. by rewrite closed_subst_vl_id; [|apply closed_to_subst].
  Qed.

  Lemma interp_subst_closed T v w ρ:
    nclosed_vl v (length Γ) →
    (⟦ Γ ⟧* ρ → ⟦ T.|[v/] ⟧ ρ w ∗-∗ ⟦ T ⟧ (v.[to_subst ρ] :: ρ) w)%I.
  Proof.
    iIntros (Hcl) "#Hg".
    iPoseProof (interp_env_len_agree with "Hg") as "%"; move: H => HlenEq; rewrite <- HlenEq in *.
    by iApply interp_subst_closed_aux.
  Qed.

End logrel_binding_lemmas.
