From iris.proofmode Require Import tactics.
From D Require Import tactics proofmode_extra.
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

Section fundamental.
  Context `{!dotG Σ}.
  Context `{hasStampTable: stampTable}.

  (* XXX these statements point out we need to realign the typing judgemnts. *)
  Lemma fundamental_dm_typed Γ V d T (HT: Γ |d V ⊢ d : T):
    wellMapped getStampTable -∗ TLater V :: Γ ⊨d d : T with
  fundamental_dms_typed Γ V ds T (HT: Γ |ds V ⊢ ds : T):
    wellMapped getStampTable -∗ TLater V :: Γ ⊨ds ds : T with
  fundamental_subtype Γ T1 i T2 (HT: Γ ⊢[i] T1 <: T2):
    wellMapped getStampTable -∗ Γ ⊨[i] T1 <: T2 with
  fundamental_typed Γ e T (HT: Γ ⊢ₜ e : T):
    wellMapped getStampTable -∗ Γ ⊨ e : T.
  Proof.
    - iIntros "#Hm"; iInduction HT as [] "IHT".
      + iApply D_Typ; by [iApply fundamental_subtype | iApply extraction_to_leadsto_envD_equiv].
      + iApply idtp_vmem_i. by iApply fundamental_typed.
    - admit.
    - iIntros "#Hm"; iInduction HT as [] "IHT".
      + by iApply DSub_Refl.
      + by iApply DSub_Trans.
      + admit; by iApply DSub_Mono.
      + by iApply DSub_Index_Incr.
      + admit; by iApply DSub_Top.
      + admit; by iApply Bot_DSub.
      + by iApply And1_DSub.
      + by iApply And2_DSub.
      + by iApply DSub_And.
      + by iApply DSub_Or1.
      + by iApply DSub_Or2.
      + by iApply Or_DSub.
      + destruct p. admit; iApply Sel_Sub. admit.
      + destruct p. admit; iApply Sub_Sel. admit.
      + admit; by iApply DSub_Mu_X.
      + admit; iApply Sub_Mu_A.
      + admit; iApply Sub_Mu_B.
      + by iApply DSub_Later_Sub.
      (* Subtyping variance. PROBLEMS WITH MODALITY SWAPS! *)
      (* Putting the later around the *whole* subtyping judgment would help here. *)
      + iApply Sub_TAll_Variant_Argh. iApply "IHT". admit.
      + iIntros "/= !>" (ρ) "#Hg".
        iSpecialize ("IHT" with "Hg").
        iNext.
        iIntros (v) "#[$ #HT1]".
        iDestruct "HT1" as (d) "#[Hdl [Hcld #HT1]]".
        iExists d; repeat iSplit => //.
        iDestruct "HT1" as (vmem) "[Heq HvT1]".
        iExists vmem; repeat iSplit => //.
        (* rewrite !swap_later.
        iApply (strip_pure_laterN (S i) (nclosed_vl vmem 0)).
        * iIntros. by iApply "IHT".
        * by iApply interp_v_closed. *)
        by iApply "IHT".
      + iIntros "/= !>" (ρ) "#Hg".
        iSpecialize ("IHT" with "Hg").
        iSpecialize ("IHT1" with "Hg").
        iNext.
        iIntros (v) "#[$ #HT1]".
        iDestruct "HT1" as (d) "#[Hdl [Hcld #HT1]]".
        iExists d; repeat iSplit => //.
        iDestruct "HT1" as (φ) "[Heq #[HLT HTU]]".
        iExists φ; repeat iSplit => //.
        iNext. iModIntro. iSplitL.
        * iIntros (u) "#Hu". iApply "HLT". by iApply "IHT".
        * iIntros (u) "#Hu". iApply "IHT1". by iApply "HTU".
      + admit; iApply Sub_TAll_Cov_Distr.
      + admit; iApply Sub_TVMem_Cov_Distr.
      + admit; iApply Sub_TTMem_Cov_Distr.
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
        admit; by iApply fundamental_subtype.
      + by iApply TAnd_I.
  Admitted.

  Lemma fundamental_typed_upd Γ e T (HT: Γ ⊢ₜ e : T): (allGs ∅ -∗ |==> Γ ⊨ e : T)%I.
  Proof.
    iIntros. iApply fundamental_typed => //. by iApply (transfer ∅).
  Qed.

End fundamental.
