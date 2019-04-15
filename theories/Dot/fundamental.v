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
  fundamental_subtype Γ T1 i1 T2 i2 (HT: Γ ⊢ₜ T1, i1 <: T2, i2):
    wellMapped getStampTable -∗ Γ ⊨ [T1, i1] <: [T2, i2] with
  fundamental_typed Γ e T (HT: Γ ⊢ₜ e : T):
    wellMapped getStampTable -∗ Γ ⊨ e : T.
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
      + destruct p. iApply Sel_Sub. admit. admit.
      + destruct p. iApply Sub_Sel. admit. admit.
      + by iApply Sub_Mu_X.
      + iApply Sub_Mu_A.
      + iApply Sub_Mu_B.
      + by iApply Sub_Later_Sub.
      (* Subtyping variance. PROBLEMS WITH MODALITY SWAPS! *)
      (* Putting the later around the *whole* subtyping judgment would help here. *)
      + iIntros "/= !>" (ρ v Hcl) "#Hg #[$ HT1]".
        iDestruct "HT1" as (t) "#[Heq #HT1']".
        iExists t; iSplit => //.
        iIntros (w).
        iSpecialize ("IHT" $! _ w _ with "Hg").
        iNext.
        iIntros "!>!> #HwT2".
        iSpecialize ("IHT1" $! (w :: ρ) w _ with "[#]").
        iFrame "Hg". by iApply interp_weaken_one.
        admit.
      + iIntros "/= !>" (ρ v Hcl) "#Hg [$ #HT1]".
        iDestruct "HT1" as (d) "#[Hdl [Hcld #HT1]]".
        iExists d; repeat iSplit => //.
        iDestruct "HT1" as (vmem) "[Heq HvT1]".
        iExists vmem; repeat iSplit => //.
        rewrite !swap_later.
        iApply (strip_pure_laterN (S i) (nclosed_vl vmem 0)).
        * iIntros. by iApply "IHT".
        * by iApply interp_v_closed.
      + admit.
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
  Admitted.

  Lemma fundamental_typed_upd Γ e T (HT: Γ ⊢ₜ e : T): (allGs ∅ -∗ |==> Γ ⊨ e : T)%I.
  Proof.
    iIntros. iApply fundamental_typed => //. by iApply (transfer ∅).
  Qed.

End fundamental.
