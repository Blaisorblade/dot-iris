From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr.

Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms).

Section Sec.
  Context `{HdlangG: dlangG Σ} (Γ : sCtx Σ).

  (* Is it true that for covariant F, F[A ∧ B] = F[A] ∧ F[B]?
    Dotty assumes that, tho DOT didn't capture it.
    F[A ∧ B] <: F[A] ∧ F[B] is provable by covariance.
    Let's prove F[A] ∧ F[B] <: F[A ∧ B] in the model.
    *)
  Lemma Sub_TAll_Cov_Distr T U1 U2 i:
    Γ s⊨ oAnd (oAll T U1) (oAll T U2), i <: oAll T (oAnd U1 U2), i.
  Proof.
    iIntros "/= !>" (ρ v) "#Hg [#H1 #H2]". iNext.
    iDestruct "H1" as (t ?) "#H1"; iDestruct "H2" as (t' ->) "#H2"; simplify_eq.
    iExists _; iSplit => //.
    iIntros "!>" (w) "#HT".
    iSpecialize ("H1" with "HT").
    iSpecialize ("H2" with "HT").
    iNext. iModIntro.
    (* Oh. Dreaded conjunction rule. Tho could we use a version
    for separating conjunction? *)
    iApply wp_and. by iApply "H1". by iApply "H2".
  Qed.

  Lemma Sub_TVMem_Cov_Distr l T1 T2 i:
    Γ s⊨ oAnd (oVMem l T1) (oVMem l T2), i <: oVMem l (oAnd T1 T2), i.
  Proof.
    iIntros "/= !>" (ρ v) "#Hg [#H1 H2]". iNext.
    iDestruct "H1" as (d? pmem?) "#H1"; iDestruct "H2" as (d'? pmem'?) "#H2". objLookupDet.
    repeat (iExists _; repeat iSplit => //).
    by iApply path_wp_and; auto.
  Qed.

  Lemma Sub_TVMem_Cov_Distr_2 l T1 T2 i:
    Γ s⊨ oVMem l (oAnd T1 T2), i <: oAnd (oVMem l T1) (oVMem l T2), i.
  Proof.
    iIntros "/= !>" (ρ v) "#Hg #H". iNext.
    iDestruct "H" as (d? pmem Hlook) "H".
    rewrite -path_wp_and; iDestruct "H" as "[H1 H2]".
    iSplit; repeat (iExists _; repeat iSplit => //).
  Qed.

  (* This should also follows internally from covariance, once that's proven. *)
  Lemma Sub_TVMem_Cov_Distr_Or_1 l T1 T2 i:
    Γ s⊨ oOr (oVMem l T1) (oVMem l T2), i <: oVMem l (oOr T1 T2), i.
  Proof.
    iIntros "/= !>" (ρ v) "#Hg [#H| #H]"; iNext;
      iDestruct "H" as (d? pmem?) "#H"; repeat (iExists _; repeat iSplit => //);
      rewrite -path_wp_or; by [iLeft | iRight].
  Qed.

  Lemma Sub_TVMem_Cov_Distr_Or_2 l T1 T2 i:
    Γ s⊨ oVMem l (oOr T1 T2), i <: oOr (oVMem l T1) (oVMem l T2), i.
  Proof.
    iIntros "/= !>" (ρ v) "#Hg #H". iNext.
    iDestruct "H" as (d? pmem?) "#H"; rewrite -path_wp_or.
    iDestruct "H" as "#[H | H]"; [> iLeft | iRight];
      repeat (iExists _; repeat iSplit => //).
  Qed.

  Lemma Sub_TTMem_Cov_Distr l L U1 U2 i:
    Γ s⊨ oAnd (oTMem l L U1) (oTMem l L U2), i <: oTMem l L (oAnd U1 U2), i.
  Proof.
    iIntros "/= !>" (ρ v) "Hg [H1 H2]". iNext.
    iDestruct "H1" as (d? φ) "#[Hsφ1 [#HLφ1 #HφU1]]"; iDestruct "H2" as (d'? φ') "#[Hsφ2 [_ #HφU2]]".
    objLookupDet.
    iExists d; repeat iSplit => //.
    iExists φ; repeat iSplit => //.
    iModIntro; iSplit; iIntros (w) "Hw".
    - by iApply "HLφ1".
    - iDestruct (dm_to_type_agree vnil w with "Hsφ1 Hsφ2") as "#Hag {Hsφ1 Hsφ2 HLφ1}".
      iSplit; [iApply "HφU1" | iApply "HφU2"] => //.
      iNext. by iRewrite -"Hag".
  Qed.

  Lemma TAnd_I v T1 T2:
    Γ s⊨ tv v : T1 -∗
    Γ s⊨ tv v : T2 -∗
    Γ s⊨ tv v : oAnd T1 T2.
  Proof.
    iIntros "#HT1 #HT2 /= !>" (ρ) "#Hg".
    iApply (wp_and_val with "(HT1 Hg) (HT2 Hg)").
  Qed.

  Lemma Sub_Mono T i :
    Γ s⊨ T, i <: T, S i.
  Proof. by iIntros "!> **". Qed.

  Lemma Sub_Add_Later T i :
    Γ s⊨ T, i <: oLater T, i.
  Proof. by iIntros "!> ** !> /=". Qed.

  Lemma Sub_Later_Sub T1 T2 i j:
    Γ s⊨ T1, S i <: T2, S j -∗
    Γ s⊨ oLater T1, i <: oLater T2, j.
  Proof.
    iIntros "/= #Hsub !>" (ρ v) "#Hg #HT1".
    iSpecialize ("Hsub" $! _ v with "Hg").
    rewrite !swap_later.
    by iApply "Hsub".
  Qed.

  Lemma Later_Sub T i :
    Γ s⊨ oLater T, i <: T, S i.
  Proof. by iIntros "/= !>" (ρ v) "#HG #HT !>". Qed.

  Lemma Sub_Later T i :
    Γ s⊨ T, S i <: oLater T, i.
  Proof. by iIntros "/= !> ** !>". Qed.

  Lemma Sub_Index_Incr T U i j:
    Γ s⊨ T, i <: U, j -∗
    Γ s⊨ T, S i <: U, S j.
  Proof. iIntros "/= #Hsub !> ** !>". by iApply "Hsub". Qed.

  Lemma And1_Sub T1 T2 i: Γ s⊨ oAnd T1 T2, i <: T1, i.
  Proof. by iIntros "/= !> * ? [? ?]". Qed.
  Lemma And2_Sub T1 T2 i: Γ s⊨ oAnd T1 T2, i <: T2, i.
  Proof. by iIntros "/= !> * ? [? ?]". Qed.

  Lemma Sub_And T U1 U2 i j:
    Γ s⊨ T, i <: U1, j -∗
    Γ s⊨ T, i <: U2, j -∗
    Γ s⊨ T, i <: oAnd U1 U2, j.
  Proof.
    iIntros "/= #H1 #H2 !> * #? ?".
    by iSplit; [iApply "H1" | iApply "H2"].
  Qed.

  Lemma Sub_Or1 T1 T2 i: Γ s⊨ T1, i <: oOr T1 T2, i.
  Proof. by iIntros "!> * _ ? !> /="; eauto. Qed.
  Lemma Sub_Or2 T1 T2 i: Γ s⊨ T2, i <: oOr T1 T2, i.
  Proof. by iIntros "!> * _ ? !> /="; eauto. Qed.

  Lemma Or_Sub T1 T2 U i j:
    Γ s⊨ T1, i <: U, j -∗
    Γ s⊨ T2, i <: U, j -∗
    Γ s⊨ oOr T1 T2, i <: U, j.
  Proof. iIntros "/= #H1 #H2 !> * #Hg #[HT1 | HT2]"; by [iApply "H1" | iApply "H2"]. Qed.

  Lemma Sub_Top T i:
    Γ s⊨ T, i <: oTop, i.
  Proof. by iIntros "!> ** /=". Qed.

  Lemma Bot_Sub T i:
    Γ s⊨ oBot, i <: T, i.
  Proof. by iIntros "/= !> ** !>". Qed.
End Sec.
