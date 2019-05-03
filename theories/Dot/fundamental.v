From iris.proofmode Require Import tactics.
From D Require Import tactics proofmode_extra swap_later_impl.
From D.Dot Require Import unary_lr unary_lr_binding typing typeExtractionSem synLemmas.
From D.Dot Require Import lr_lemma lr_lemmasDefs lr_lemma_nobinding lr_lemmasTSel.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

(* Should use fresh names. *)
Ltac iDestrConjs :=
  iMatchHyp (fun H P => match P with
                        | (_ ∧ _)%I =>
                          iDestruct H as "[#HA #HB]"
                        | (_ ∗ _)%I =>
                          iDestruct H as "[#HA #HB]"
                        end).

Section swap_based_typing_lemmas.
  Context `{!dotG Σ} `{!SwapProp (iPropSI Σ)} {Γ}.
  Context `{hasStampTable: stampTable}.

  Ltac unfold_interp := idtac.
  Lemma Sub_TAllConCov T1 T2 U1 U2 i:
    Γ ⊨ [ T2, S i ] <: [ T1, S i ] -∗
    iterate TLater (S i) T2.|[ren (+1)] :: Γ ⊨ [ U1, S i ] <: [ U2, S i ] -∗
    Γ ⊨ [ TAll T1 U1, i ] <: [ TAll T2 U2, i ].
  Proof.
    rewrite iterate_S /=.
    iIntros "#HsubT #HsubU /= !>" (ρ v Hcl) "#Hg".
    unfold_interp.
    iIntros "[$ #HT1]".
    iDestruct "HT1" as (t) "#[Heq #HT1]". iExists t; iSplit => //.
    iIntros (w).
    rewrite -!mlaterN_pers -mlater_impl -mlaterN_impl !swap_later.
    iIntros "!> #HwT2".
    iApply (strip_pure_laterN_impl (S i) (nclosed_vl w 0)); first last.
      by iApply interp_v_closed.
    iIntros (Hclw).
    iSpecialize ("HsubT" $! ρ w Hclw with "Hg HwT2").
    iAssert (□ ▷ ▷^i (∀ v0, ⟦ U1 ⟧ (w :: ρ) v0 →
        ⟦ U2 ⟧ (w :: ρ) v0))%I as "#HsubU'". {
      iIntros (v0); rewrite -!mlaterN_impl -mlater_impl.
      iIntros "!> #HUv0".
      iApply (strip_pure_laterN_impl (S i) (nclosed_vl v0 0)); first last.
        by iApply interp_v_closed.
      iIntros (Hclv0).
      iApply ("HsubU" $! (w :: ρ) v0) => //.
      unfold_interp; rewrite iterate_TLater_later //.
      iFrame "Hg %". by iApply interp_weaken_one.
    }
    iClear "HsubU". iNext 1; iNext i. iApply wp_wand.
    - iApply "HT1". by iApply "HsubT".
    - iIntros (u) "#HuU1". by iApply "HsubU'".
  Qed.

  Import uPred.
  Lemma Sub_TTMem_Variant L1 L2 U1 U2 i l:
    Γ ⊨ [L2, S i] <: [L1, S i] -∗
    Γ ⊨ [U1, S i] <: [U2, S i] -∗
    Γ ⊨ [TTMem l L1 U1, i] <: [TTMem l L2 U2, i].
  Proof.
    iIntros "#IHT #IHT1 /= !>" (ρ v Hcl) "#Hg".
    unfold_interp.
    iIntros "[$ #HT1]".
    iDestruct "HT1" as (d) "[Hl2 [? H]]".
    iDestruct "H" as (φ) "#[Hφl [HLφ #HφU]]".
    setoid_rewrite <- later_laterN.
    setoid_rewrite mlaterN_impl.
    iExists d; repeat iSplit => //.
    iExists φ; repeat iSplitL => //;
      rewrite -!mlaterN_pers;
      iIntros "!>" (w Hclw);
      iSpecialize ("IHT" $! ρ w Hclw with "Hg");
      iSpecialize ("IHT1" $! ρ w Hclw with "Hg");
      iNext; iIntros.
    - iApply "HLφ" => //. by iApply "IHT".
    - iApply "IHT1". by iApply "HφU".
  Qed.

  Lemma Sub_TVMem_Variant T1 T2 i l:
    Γ ⊨ [T1, S i] <: [T2, S i] -∗
    Γ ⊨ [TVMem l T1, i] <: [TVMem l T2, i].
  Proof.
    iIntros "#IHT /= !>" (ρ v Hcl) "#Hg [$ #HT1]".
    iDestruct "HT1" as (d) "#[Hdl [Hcld #HT1]]".
    iExists d; repeat iSplit => //.
    iDestruct "HT1" as (vmem) "[Heq HvT1]".
    iExists vmem; repeat iSplit => //.
    rewrite !swap_later.
    iApply (strip_pure_laterN_wand (S i) (nclosed_vl vmem 0)).
    - iIntros. by iApply "IHT".
    - by iApply interp_v_closed.
  Qed.
End swap_based_typing_lemmas.

Section fundamental.
  Context `{!dotG Σ} `{!SwapProp (iPropSI Σ)}.
  Context `{hasStampTable: stampTable}.

  (* XXX these statements point out we need to realign the typing judgemnts. *)
  Lemma fundamental_dm_typed Γ V d T (HT: Γ |d V ⊢ d : T):
    wellMapped getStampTable -∗ TLater V :: Γ ⊨d d : T with
  fundamental_dms_typed Γ V ds T (HT: Γ |ds V ⊢ ds : T):
    wellMapped getStampTable -∗ TLater V :: Γ ⊨ds ds : T with
  fundamental_subtype Γ T1 i1 T2 i2 (HT: Γ ⊢ₜ T1, i1 <: T2, i2):
    wellMapped getStampTable -∗ Γ ⊨ [T1, i1] <: [T2, i2] with
  fundamental_typed Γ e T (HT: Γ ⊢ₜ e : T):
    wellMapped getStampTable -∗ Γ ⊨ e : T with
  fundamental_path_typed Γ v T i (HT : Γ ⊢ₚ pv v : T, i):
    wellMapped getStampTable -∗ Γ ⊨ tv v : T, i.
  Proof.
    - iIntros "#Hm"; iInduction HT as [] "IHT".
      + iApply D_Typ;
        last by iApply extraction_to_leadsto_envD_equiv.
        by iApply fundamental_subtype.
        by iApply fundamental_subtype.
      + iApply idtp_vmem_i. by iApply fundamental_typed.
    - admit.
    - iIntros "#Hm"; iInduction HT as [] "IHT".
      + by iApply Sub_Refl.
      + by iApply Sub_Trans.
      + by iApply Later_Sub.
      + by iApply Sub_Later.
      + by iApply Sub_Mono.
      + by iApply Sub_Index_Incr.
      + by iApply Sub_Top.
      + by iApply Bot_Sub.
      + by iApply And1_Sub.
      + by iApply And2_Sub.
      + by iApply Sub_And.
      + by iApply Sub_Or1.
      + by iApply Sub_Or2.
      + by iApply Or_Sub.
      + destruct p.
        iApply Sel_Sub. by iApply fundamental_path_typed.
        admit.
      + destruct p.
        iApply Sub_Sel. by iApply fundamental_path_typed.
        admit.
      + by iApply Sub_Mu_X.
      + iApply Sub_Mu_A.
      + iApply Sub_Mu_B.
      + by iApply Sub_Later_Sub.
      + by iApply Sub_TAllConCov.
      + by iApply Sub_TVMem_Variant.
      + by iApply Sub_TTMem_Variant.
      + iApply Sub_TAll_Cov_Distr.
      + iApply Sub_TVMem_Cov_Distr.
      + iApply Sub_TTMem_Cov_Distr.
    - iIntros "#Hm"; iInduction HT as [] "IHT".
      + by iApply T_Forall_Ex.
      + by iApply T_Forall_E.
      + by iApply T_Mem_E.
      + by iApply TMu_E.
      + by iApply T_Forall_I.
      + iApply T_New_I.
        by iApply fundamental_dms_typed.
      + by iApply TMu_I.
      + by iApply T_Nat_I.
      + by iApply T_Var.
      + iApply T_Sub => //.
        by iApply fundamental_subtype.
      + by iApply TAnd_I.
    - admit.
  Admitted.

  Lemma fundamental_typed_upd Γ e T (HT: Γ ⊢ₜ e : T): (allGs ∅ -∗ |==> Γ ⊨ e : T)%I.
  Proof.
    iIntros. iApply fundamental_typed => //. by iApply (transfer ∅).
  Qed.

End fundamental.
