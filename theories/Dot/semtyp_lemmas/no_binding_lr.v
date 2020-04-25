From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr.

Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms).
Set Suggest Proof Using.
Set Default Proof Using "Type".

Section Sec.
  Context `{HdlangG: !dlangG Σ} (Γ : sCtx Σ).

  (* Only provable semantically *)
  Lemma sAnd_Or_Sub_Distr {S T U i}: ⊢ Γ s⊨ oAnd (oOr S T) U , i <: oOr (oAnd S U) (oAnd T U), i.
  Proof. iIntros "!> %% #Hg [[HS|HT] Hu] !> /="; [iLeft|iRight]; iFrame. Qed.

  (** Also derivable syntactically; see [iOr_And_Sub_Distr_inv]. But much easier to
  derive in the model. *)
  Lemma sAnd_Or_Sub_Distr_inv {S T U i}: ⊢ Γ s⊨ oAnd (oOr S U) (oOr T U), i <: oOr (oAnd S T) U , i.
  Proof. iIntros "!> %% #Hg [[HS|HT] [HT'|HU]] !> /="; eauto with iFrame. Qed.

  (* Is it true that for covariant F, F[A ∧ B] = F[A] ∧ F[B]?
    Dotty assumes that, tho DOT didn't capture it.
    F[A ∧ B] <: F[A] ∧ F[B] is provable by covariance.
    Let's prove F[A] ∧ F[B] <: F[A ∧ B] in the model.
    *)
  Lemma sAnd_All_Sub_Distr T U1 U2 i:
    ⊢ Γ s⊨ oAnd (oAll T U1) (oAll T U2), i <: oAll T (oAnd U1 U2), i.
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

  Lemma sAnd_Fld_Sub_Distr l T1 T2 i:
    ⊢ Γ s⊨ oAnd (cVMem l T1) (cVMem l T2), i <: cVMem l (oAnd T1 T2), i.
  Proof.
    iIntros "/= !>" (ρ v) "#Hg [#H1 H2]". iNext.
    iDestruct "H1" as (d? pmem?) "#H1"; iDestruct "H2" as (d'? pmem'?) "#H2". objLookupDet.
    repeat (iExists _; repeat iSplit => //).
    by iApply (path_wp_and' with "H1 H2").
  Qed.

  Lemma sAnd_Fld_Sub_Distr_2 l T1 T2 i:
    ⊢ Γ s⊨ cVMem l (oAnd T1 T2), i <: oAnd (cVMem l T1) (cVMem l T2), i.
  Proof.
    iIntros "/= !>" (ρ v) "#Hg #H". iNext.
    iDestruct "H" as (d? pmem Hlook) "H".
    rewrite -path_wp_and; iDestruct "H" as "[H1 H2]".
    iSplit; repeat (iExists _; repeat iSplit => //).
  Qed.

  (* This should also follows internally from covariance, once that's proven. *)
  Lemma sAnd_Fld_Sub_Distr_Or_1 l T1 T2 i:
    ⊢ Γ s⊨ oOr (cVMem l T1) (cVMem l T2), i <: cVMem l (oOr T1 T2), i.
  Proof.
    iIntros "/= !>" (ρ v) "#Hg [#H| #H]"; iNext;
      iDestruct "H" as (d? pmem?) "#H"; repeat (iExists _; repeat iSplit => //);
      rewrite -path_wp_or; by [iLeft | iRight].
  Qed.

  Lemma sAnd_Fld_Sub_Distr_Or_2 l T1 T2 i:
    ⊢ Γ s⊨ cVMem l (oOr T1 T2), i <: oOr (cVMem l T1) (cVMem l T2), i.
  Proof.
    iIntros "/= !>" (ρ v) "#Hg #H". iNext.
    iDestruct "H" as (d? pmem?) "#H"; rewrite -path_wp_or.
    iDestruct "H" as "#[H | H]"; [> iLeft | iRight];
      repeat (iExists _; repeat iSplit => //).
  Qed.

  Lemma sAnd_Typ_Sub_Distr l L U1 U2 i:
    ⊢ Γ s⊨ oAnd (cTMem l L U1) (cTMem l L U2), i <: cTMem l L (oAnd U1 U2), i.
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

  Lemma sT_And_I v T1 T2:
    Γ s⊨ tv v : T1 -∗
    Γ s⊨ tv v : T2 -∗
    Γ s⊨ tv v : oAnd T1 T2.
  Proof.
    iIntros "#HT1 #HT2 /= !>" (ρ) "#Hg".
    iApply (wp_and_val with "(HT1 Hg) (HT2 Hg)").
  Qed.

  Lemma sSub_Add_Later T i :
    ⊢ Γ s⊨ T, i <: oLater T, i.
  Proof. by iIntros "!> ** !> /=". Qed.

  Lemma sSub_Later_Sub T1 T2 i j:
    Γ s⊨ T1, S i <: T2, S j -∗
    Γ s⊨ oLater T1, i <: oLater T2, j.
  Proof.
    iIntros "/= #Hsub !>" (ρ v) "#Hg #HT1".
    iSpecialize ("Hsub" $! _ v with "Hg").
    rewrite !swap_later.
    by iApply "Hsub".
  Qed.

  Lemma sLater_Sub T i :
    ⊢ Γ s⊨ oLater T, i <: T, S i.
  Proof. by iIntros "/= !>" (ρ v) "#HG #HT !>". Qed.

  Lemma sSub_Later T i :
    ⊢ Γ s⊨ T, S i <: oLater T, i.
  Proof. by iIntros "/= !> ** !>". Qed.

  Lemma sSub_Index_Incr T U i j:
    Γ s⊨ T, i <: U, j -∗
    Γ s⊨ T, S i <: U, S j.
  Proof. iIntros "/= #Hsub !> ** !>". by iApply "Hsub". Qed.

  Lemma sSub_Later_Mono T U i j:
    Γ s⊨ T, i <: U, j -∗
    Γ s⊨ oLater T, i <: oLater U, j.
  Proof.
    iIntros "/= #Hsub !> %% Hg HT". rewrite !swap_later.
    by iApply ("Hsub" with "Hg HT").
  Qed.

  Lemma sAnd1_Sub T1 T2 i: ⊢ Γ s⊨ oAnd T1 T2, i <: T1, i.
  Proof. by iIntros "/= !> * ? [? ?]". Qed.
  Lemma sAnd2_Sub T1 T2 i: ⊢ Γ s⊨ oAnd T1 T2, i <: T2, i.
  Proof. by iIntros "/= !> * ? [? ?]". Qed.

  Lemma sSub_And T U1 U2 i j:
    Γ s⊨ T, i <: U1, j -∗
    Γ s⊨ T, i <: U2, j -∗
    Γ s⊨ T, i <: oAnd U1 U2, j.
  Proof.
    iIntros "/= #H1 #H2 !> * #? ?".
    by iSplit; [iApply "H1" | iApply "H2"].
  Qed.

  Lemma sSub_Or1 T1 T2 i: ⊢ Γ s⊨ T1, i <: oOr T1 T2, i.
  Proof. by iIntros "!> * _ ? !> /="; eauto. Qed.
  Lemma sSub_Or2 T1 T2 i: ⊢ Γ s⊨ T2, i <: oOr T1 T2, i.
  Proof. by iIntros "!> * _ ? !> /="; eauto. Qed.

  Lemma sOr_Sub T1 T2 U i j:
    Γ s⊨ T1, i <: U, j -∗
    Γ s⊨ T2, i <: U, j -∗
    Γ s⊨ oOr T1 T2, i <: U, j.
  Proof. iIntros "/= #H1 #H2 !> * #Hg #[HT1 | HT2]"; by [iApply "H1" | iApply "H2"]. Qed.

  Lemma sSub_Top T i:
    ⊢ Γ s⊨ T, i <: oTop, i.
  Proof. by iIntros "!> ** /=". Qed.

  Lemma sBot_Sub T i:
    ⊢ Γ s⊨ oBot, i <: T, i.
  Proof. by iIntros "/= !> ** !>". Qed.
End Sec.
