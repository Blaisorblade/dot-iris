From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
From D Require Import proofmode_extra.
From D.Dot Require Import unary_lr.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

Section Sec.
  Context `{HdlangG: dlangG Σ} Γ.

  (* Is it true that for covariant F, F[A ∧ B] = F[A] ∧ F[B]?
    Dotty assumes that, tho DOT didn't capture it.
    F[A ∧ B] <: F[A] ∧ F[B] is provable by covariance.
    Let's prove F[A] ∧ F[B] <: F[A ∧ B] in the model.
    *)
  Lemma Sub_TAll_Cov_Distr T U1 U2 i:
    Γ ⊨ [TAnd (TAll T U1) (TAll T U2), i] <: [TAll T (TAnd U1 U2), i].
  Proof.
    iIntros "/= !>" (ρ v Hcl) "#Hg [[$ #H1] #[_ H2]]". iNext.
    iDestruct "H1" as (t ?) "#H1"; iDestruct "H2" as (t' ->) "#H2"; simplify_eq.
    iExists _; iSplit => //.
    iIntros "!>!>" (w) "#HT".
    (* Oh. Dreaded conjunction rule. Tho could we use a version
    for separating conjunction? *)
    iApply wp_and. by iApply "H1". by iApply "H2".
  Qed.

  Lemma Sub_TVMem_Cov_Distr l T1 T2 i:
    Γ ⊨ [TAnd (TVMem l T1) (TVMem l T2), i] <: [TVMem l (TAnd T1 T2), i].
  Proof.
    iIntros "/= !>" (ρ v Hcl) "#Hg [[$ #H1] #[_ H2]]". iNext.
    iDestruct "H1" as (d? vmem?) "#H1"; iDestruct "H2" as (d'? vmem'?) "#H2". objLookupDet.
    repeat (iExists _; repeat iSplit => //).
  Qed.

  Lemma Sub_TVMem_Cov_Distr_2 l T1 T2 i:
    Γ ⊨ [TVMem l (TAnd T1 T2), i] <: [TAnd (TVMem l T1) (TVMem l T2), i].
  Proof.
    iIntros "/= !>" (ρ v Hcl) "#Hg [$ #H]". iNext.
    iDestruct "H" as (d? vmem?) "#[H1 H2]".
    iSplit; repeat (iExists _; repeat iSplit => //).
  Qed.

  (* This should also follows internally from covariance, once that's proven. *)
  Lemma Sub_TVMem_Cov_Distr_Or_1 l T1 T2 i:
    Γ ⊨ [TOr (TVMem l T1) (TVMem l T2), i] <: [TVMem l (TOr T1 T2), i].
  Proof.
    iIntros "/= !>" (ρ v Hcl) "#Hg [[$ #H]| [$ #H]]"; iNext;
    iDestruct "H" as (d? vmem?) "#H";
    repeat (iExists _; repeat iSplit => //); by [iLeft | iRight].
  Qed.

  Lemma Sub_TVMem_Cov_Distr_Or_2 l T1 T2 i:
    Γ ⊨ [TVMem l (TOr T1 T2), i] <: [TOr (TVMem l T1) (TVMem l T2), i].
  Proof.
    iIntros "/= !>" (ρ v Hcl) "#Hg [$ #H]". iNext.
    iDestruct "H" as (d? vmem?) "#[H | H]"; [> iLeft | iRight];
      repeat (iExists _; repeat iSplit => //).
  Qed.

  Lemma Sub_TTMem_Cov_Distr l L U1 U2 i:
    Γ ⊨ [TAnd (TTMem l L U1) (TTMem l L U2), i] <: [TTMem l L (TAnd U1 U2), i].
  Proof.
    iIntros "/= !>" (ρ v Hcl) "Hg [[$ H1] [_ H2]]". iNext.
    iDestruct "H1" as (d? φ) "#[Hsφ1 [#HLφ1 #HφU1]]"; iDestruct "H2" as (d'? φ') "#[Hsφ2 [_ #HφU2]]".
    objLookupDet.
    iExists d; repeat iSplit => //.
    iExists φ; repeat iSplit => //.
    iModIntro; iSplitL; iIntros (w Hclw) "Hw".
    - by iApply "HLφ1".
    - iDestruct (stored_pred_agree d _ _ w with "Hsφ1 Hsφ2") as "#Hag".
      iClear "Hsφ1 Hsφ2 HLφ1".
      iSplit; [iApply "HφU1" | iApply "HφU2"] => //.
      iNext. by iRewrite -"Hag".
  Qed.

  Lemma TAnd_I v T1 T2:
    Γ ⊨ tv v : T1 -∗
    Γ ⊨ tv v : T2 -∗
    Γ ⊨ tv v : TAnd T1 T2.
  Proof.
    iIntros "#[$ #HT1] #[_ #HT2] /= !>" (ρ) "#Hg".
    iApply (wp_and_val with "(HT1 Hg) (HT2 Hg)").
  Qed.

  Lemma Sub_Mono T i :
    (Γ ⊨ [T, i] <: [T, S i])%I.
  Proof. by iIntros "!> **". Qed.

  Lemma Sub_Later_Sub T1 T2 i:
    Γ ⊨ [T1, S i] <: [T2, S i] -∗
    Γ ⊨ [TLater T1, i] <: [TLater T2, i].
  Proof.
    iIntros "/= #Hsub !>" (ρ v Hclv) "#Hg #[_ HT1]"; iFrame "%".
    iSpecialize ("Hsub" $! _ v Hclv with "Hg").
    rewrite !swap_later.
    by iApply "Hsub".
  Qed.

  Lemma Later_Sub T i :
    (Γ ⊨ [TLater T, i] <: [T, S i])%I.
  Proof. by iIntros "/= !>" (ρ v Hclv) "#HG #[_ HT] !>". Qed.

  Lemma Sub_Later T i :
    (Γ ⊨ [T, S i] <: [TLater T, i])%I.
  Proof. iIntros "/= !> ** !>". naive_solver. Qed.

  Lemma Sub_Index_Incr T U i j:
    (Γ ⊨ [T, i] <: [U, j] →
     Γ ⊨ [T, S i] <: [U, S j])%I.
  Proof. iIntros "/= #Hsub !> ** !>". by iApply "Hsub". Qed.

  Lemma And1_Sub T1 T2 i: Γ ⊨ [TAnd T1 T2, i] <: [T1, i].
  Proof. by iIntros "/= !> * ? ? [? ?]". Qed.
  Lemma And2_Sub T1 T2 i: Γ ⊨ [TAnd T1 T2, i] <: [T2, i].
  Proof. by iIntros "/= !> * ? ? [? ?]". Qed.

  (* Lemma stp_andi T1 T2 ρ v: *)
  (*   ⟦T1⟧ ρ v -∗ *)
  (*   ⟦T2⟧ ρ v -∗ *)
  (*   ⟦TAnd T1 T2⟧ ρ v. *)
  (* Proof. iIntros; by iSplit. Qed. *)

  Lemma Sub_And S T1 T2 i j:
    Γ ⊨ [S, i] <: [T1, j] -∗
    Γ ⊨ [S, i] <: [T2, j] -∗
    Γ ⊨ [S, i] <: [TAnd T1 T2, j].
  Proof.
    iIntros "/= #H1 #H2 !> * % #? ?".
    by iSplit; [iApply "H1" | iApply "H2"].
  Qed.

  Lemma Sub_Or1 T1 T2 i: Γ ⊨ [T1, i] <: [TOr T1 T2, i].
  Proof. by iIntros "/= !> * _ _ ? !>"; eauto. Qed.
  Lemma Sub_Or2 T1 T2 i: Γ ⊨ [T2, i] <: [TOr T1 T2, i].
  Proof. by iIntros "/= !> * _ _ ? !>"; eauto. Qed.

  Lemma Or_Sub S T1 T2 i j:
    Γ ⊨ [T1, i] <: [S, j] -∗
    Γ ⊨ [T2, i] <: [S, j] -∗
    Γ ⊨ [TOr T1 T2, i] <: [S, j].
  Proof. iIntros "/= #H1 #H2 !> * #Hcl #Hg #[HT1 | HT2]"; by [iApply "H1" | iApply "H2"]. Qed.

  Lemma Sub_Top T i:
    Γ ⊨ [T, i] <: [TTop, i].
  Proof. by iIntros "!> ** /=". Qed.

  Lemma Bot_Sub T i:
    Γ ⊨ [TBot, i] <: [T, i].
  Proof. by iIntros "/= !> ** !>". Qed.

  Lemma T_Nat_I n: Γ ⊨ tv (vnat n): TNat.
  Proof.
    iSplit => //=; iIntros "!> * _"; rewrite -wp_value; eauto.
  Qed.
End Sec.
