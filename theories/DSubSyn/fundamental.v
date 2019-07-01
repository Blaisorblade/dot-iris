(* This files proves the fundamental lemma for D<:.

   It also proves any typing lemmas that depend on swap_later_impl.v (extra
   modality swap lemmas, depending on `CmraSwappable` instances for Σ). They are
   kept separate, because we might have to extend Σ with resources without a
   CmraSwappable instance.
 *)
From iris.proofmode Require Import tactics.
From D Require Import proofmode_extra swap_later_impl.
From D.DSubSyn Require Import unary_lr_binding lr_lemma.

Implicit Types (L T U: ty) (v: vl) (e: tm) (Γ : ctx).

Section swap_based_typing_lemmas.
  Context `{!dsubSynG Σ} `{!SwapProp (iPropSI Σ)} {Γ}.

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
    iAssert (□ ▷ ▷^i (∀ v0, ⟦ U1 ⟧ (w .: to_subst ρ) v0 →
        ⟦ U2 ⟧ (w .: to_subst ρ) v0))%I as "#HsubU'". {
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

  Lemma DSub_TAll_ConCov T1 T2 U1 U2 i:
    Γ ⊨[S i] T2 <: T1 -∗
    iterate TLater (S i) T2.|[ren (+1)] :: Γ ⊨[S i] U1 <: U2 -∗
    Γ ⊨[i] TAll T1 U1 <: TAll T2 U2.
  Proof.
    rewrite iterate_S /=.
    iIntros "#HsubT #HsubU /= !>" (ρ) "#Hg"; iIntros (v).
    unfold_interp; rewrite -mlaterN_impl.
    iIntros "[$ #HT1]".
    iDestruct "HT1" as (t) "#[Heq #HT1]"; iExists t; iSplit => //.
    iIntros (w).
    rewrite -!mlaterN_pers -!laterN_later/= -!mlaterN_impl -!mlater_impl.
    iIntros "!> #HwT2".
    iApply (strip_pure_laterN_impl (S i) (nclosed_vl w 0)); first last.
      by iApply interp_v_closed.
    iIntros (Hclw).
    iSpecialize ("HsubT" with "Hg").
    iSpecialize ("HsubU" $! (w :: ρ) with "[#]"). {
      unfold_interp; rewrite iterate_TLater_later //.
      iFrame "#%". by iApply interp_weaken_one.
    }
    iNext; iNext i. iApply wp_wand.
    - iApply "HT1". by iApply "HsubT".
    - iIntros (u) "#HuU1". by iApply "HsubU".
  Qed.

  Lemma Sub_TTMem_Variant L1 L2 U1 U2 i:
    Γ ⊨ [L2, S i] <: [L1, S i] -∗
    Γ ⊨ [U1, S i] <: [U2, S i] -∗
    Γ ⊨ [TTMem L1 U1, i] <: [TTMem L2 U2, i].
  Proof.
    iIntros "#IHT #IHT1 /= !>" (ρ v Hcl) "#Hg".
    unfold_interp.
    iIntros "[$ #HT1]".
    iDestruct "HT1" as (φ) "#[Hφl [HLφ #HφU]]".
    setoid_rewrite <- later_laterN.
    setoid_rewrite mlaterN_impl.
    iExists φ; repeat iSplitL; first done;
      rewrite -!mlaterN_pers;
      iIntros "!>" (w Hclw);
      iSpecialize ("IHT" $! ρ w Hclw with "Hg");
      iSpecialize ("IHT1" $! ρ w Hclw with "Hg");
      iNext; iIntros.
    - iApply "HLφ" => //. by iApply "IHT".
    - iApply "IHT1". by iApply "HφU".
  Qed.
End swap_based_typing_lemmas.

From D.DSubSyn Require Import typing.

Section Fundamental.
  Context `{!dsubSynG Σ} `{!SwapProp (iPropSI Σ)}.

  Lemma fundamental_subtype Γ T1 i1 T2 i2 (HT: Γ ⊢ₜ T1, i1 <: T2, i2):
    Γ ⊨ [T1, i1] <: [T2, i2]
  with
  fundamental_typed Γ e T (HT: Γ ⊢ₜ e : T):
    Γ ⊨ e : T.
  Proof.
    - iInduction HT as [] "IHT".
      + by iApply Sub_Refl.
      + by iApply Sub_Trans.
      + by iIntros "!> **".
      (* + by iApply Sub_Later.
      + by iApply Sub_Mono. *)
      + by iApply Sub_Index_Incr.
      + by iApply Sub_Top.
      + by iApply Bot_Sub.
      + iApply Sel_Sub. by iApply fundamental_typed.
      + iApply Sub_Sel. by iApply fundamental_typed.
      + by iApply Sub_TAllConCov.
      + by iApply Sub_TTMem_Variant.
    - iInduction HT as [] "IHT".
      + by iApply T_Forall_Ex.
      + by iApply T_Forall_E.
      + by iApply T_Forall_I.
      (* + iApply T_New_I.
        by iApply fundamental_dms_typed.
      + by iApply TMu_I. *)
      + by iApply T_Nat_I.
      + by iApply T_Var.
      + iApply T_Sub => //.
        by iApply fundamental_subtype.
      + iApply T_Vty_abs_I => //;
        by iApply fundamental_subtype.
      + by iApply T_Vty_I.
    Qed.
End Fundamental.

From D.pure_program_logic Require Import adequacy.

Theorem adequacy Σ `{HdsubG: dsubSynG Σ} `{!SwapProp (iPropSI Σ)} e e' thp σ σ' T:
  (forall `{dsubSynG Σ} `{SwapProp (iPropSI Σ)}, True ⊢ [] ⊨ e : T) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hlog ??. cut (adequate NotStuck e σ (λ _ _, True)); first (intros [_ ?]; eauto).
  eapply (wp_adequacy Σ) => /=.
  iIntros (?) "!>". iExists (λ _ _, True%I); iSplit=> //.
  iPoseProof (Hlog with "[//]") as "#[_ #Hlog]".
  iEval (replace e with (e.|[to_subst []]) by by asimpl).
  iApply wp_wand; by [iApply "Hlog" | auto].
Qed.

Instance dsubSynG_empty: dsubSynG #[].

Corollary type_soundness e e' thp σ σ' T:
  ([] ⊢ₜ e : T) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros; eapply (adequacy #[]) => //; iIntros.
  by iApply fundamental_typed.
Qed.
