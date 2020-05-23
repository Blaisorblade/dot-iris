(** * Semantic lemmas for double-delay subtyping. *)
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

From D Require Import iris_prelude succ_notation swap_later_impl proper.
From D.Dot Require Import rules path_repl unary_lr.

Section StpLemmas.
  Context `{HdotG: !dlangG Σ}.

  Lemma sSub_Top Γ T i:
    ⊢ Γ s⊨ T, i <: oTop, i.
  Proof. by iIntros "!> ** /=". Qed.

  Lemma sBot_Sub Γ T i:
    ⊢ Γ s⊨ oBot, i <: T, i.
  Proof. by iIntros "/= !> ** !>". Qed.

  Lemma sAnd1_Sub Γ T1 T2 i: ⊢ Γ s⊨ oAnd T1 T2, i <: T1, i.
  Proof. by iIntros "/= !> * ? [? ?]". Qed.
  Lemma sAnd2_Sub Γ T1 T2 i: ⊢ Γ s⊨ oAnd T1 T2, i <: T2, i.
  Proof. by iIntros "/= !> * ? [? ?]". Qed.

  Lemma sSub_And Γ T U1 U2 i j:
    Γ s⊨ T, i <: U1, j -∗
    Γ s⊨ T, i <: U2, j -∗
    Γ s⊨ T, i <: oAnd U1 U2, j.
  Proof.
    iIntros "/= #H1 #H2 !> * #? ?".
    by iSplit; [iApply "H1" | iApply "H2"].
  Qed.

  Lemma sSub_Or1 Γ T1 T2 i: ⊢ Γ s⊨ T1, i <: oOr T1 T2, i.
  Proof. by iIntros "!> * _ ? !> /="; eauto. Qed.
  Lemma sSub_Or2 Γ T1 T2 i: ⊢ Γ s⊨ T2, i <: oOr T1 T2, i.
  Proof. by iIntros "!> * _ ? !> /="; eauto. Qed.

  Lemma sOr_Sub Γ T1 T2 U i j:
    Γ s⊨ T1, i <: U, j -∗
    Γ s⊨ T2, i <: U, j -∗
    Γ s⊨ oOr T1 T2, i <: U, j.
  Proof. iIntros "/= #H1 #H2 !> * #Hg #[HT1 | HT2]"; by [iApply "H1" | iApply "H2"]. Qed.

  Lemma sDistr_And_Or_Sub {Γ S T U i}:
    ⊢ Γ s⊨ oAnd (oOr S T) U , i <: oOr (oAnd S U) (oAnd T U), i.
  Proof. iIntros "!> %% #Hg [[HS|HT] Hu] !> /="; [iLeft|iRight]; iFrame. Qed.

  Lemma sSub_Add_Later Γ T i :
    ⊢ Γ s⊨ T, i <: oLater T, i.
  Proof. by iIntros "!> ** !> /=". Qed.

  Lemma sLater_Sub Γ T i :
    ⊢ Γ s⊨ oLater T, i <: T, S i.
  Proof. by iIntros "/= !> %ρ %v #HG #HT !>". Qed.

  Lemma sSub_Later Γ T i :
    ⊢ Γ s⊨ T, S i <: oLater T, i.
  Proof. by iIntros "/= !> ** !>". Qed.

  (** ** Subtyping for type selections. *)
  Lemma sSub_Sel {Γ L U p l i}:
    Γ s⊨p p : cTMem l L U, i -∗
    Γ s⊨ oLater L, i <: oSel p l, i.
  Proof.
    iIntros "/= #Hp !> %ρ %v Hg #HL"; iSpecialize ("Hp" with "Hg"); iNext i.
    iApply (path_wp_wand with "Hp"); iIntros (w).
    iApply (vl_sel_lb with "HL").
  Qed.

  Lemma sSel_Sub {Γ L U p l i}:
    Γ s⊨p p : cTMem l L U, i -∗
    Γ s⊨ oSel p l, i <: oLater U, i.
  Proof.
    iIntros "#Hp !> %ρ %v Hg Hφ"; iSpecialize ("Hp" with "Hg"); iNext i.
    iDestruct (path_wp_agree with "Hp Hφ") as (w Hw) "[Hp Hφ]".
    iApply (vl_sel_ub with "Hφ Hp").
  Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂ᶻ
     ----------------------------------------------- (<:-μ-X)
     Γ ⊨ μ (x: T₁ˣ) <: μ(x: T₂ˣ)
  *)
  Lemma sMu_Sub_Mu {Γ T1 T2 i j} :
    oLaterN i T1 :: Γ s⊨ T1, i <: T2, j -∗
    Γ s⊨ oMu T1, i <: oMu T2, j.
  Proof.
    iIntros "/= #Hstp !> %ρ %v #Hg #HT1".
    iApply ("Hstp" $! (v .: ρ) v with "[$Hg $HT1] [$HT1]").
  Qed.

  Lemma Mu_Sub_Mu {Γ} T1 T2 i j:
    iterate TLater i T1 :: Γ ⊨ T1, i <: T2, j -∗
    Γ ⊨ TMu T1, i <: TMu T2, j.
  Proof.
    rewrite /istpi -sMu_Sub_Mu.
    by rewrite fmap_cons (iterate_TLater_oLater i T1).
  Qed.

  (**
     x ∉ fv T
     -----------------------------------------------
     Γ ⊨ mu x: T <: T    Γ ⊨ T <: mu(x: T)
  *)

  (** Novel subtyping rules. [Sub_Bind_1] and [Sub_Bind_2] become
  derivable. *)
  Lemma sMu_Sub {Γ T i} : ⊢ Γ s⊨ oMu (shift T), i <: T, i.
  Proof. iIntros "!> **". by rewrite oMu_shift. Qed.

  Lemma Mu_Sub {Γ} T i: ⊢ Γ ⊨ TMu (shift T), i <: T, i.
  Proof.
    rewrite /istpi; cbn -[sstpi].
    rewrite (interp_subst_commute T (ren (+1))).
    apply sMu_Sub.
  Qed.


  Lemma sSub_Mu {Γ T i} : ⊢ Γ s⊨ T, i <: oMu (shift T), i.
  Proof. iIntros "!> **". by rewrite oMu_shift. Qed.

  Lemma Sub_Mu {Γ} T i: ⊢ Γ ⊨ T, i <: TMu (shift T), i.
  Proof.
    rewrite /istpi; cbn -[sstpi].
    rewrite (interp_subst_commute T (ren (+1))).
    apply sSub_Mu.
  Qed.


  Lemma sFld_Sub_Fld' {Γ T1 T2 i j l}:
    Γ s⊨ T1, i <: T2, j + i -∗
    Γ s⊨ cVMem l T1, i <: cVMem l T2, j + i.
  Proof.
    iIntros "#Hsub /= !> %ρ %v #Hg #HT1". setoid_rewrite laterN_plus.
    iDestruct "HT1" as (d) "#[Hdl #HT1]".
    iExists d; repeat iSplit => //.
    iDestruct "HT1" as (pmem) "[Heq HvT1]".
    iExists pmem; repeat iSplit => //; rewrite !path_wp_eq.
    iDestruct "HvT1" as (w) "[Hv HvT1]"; iExists w; iFrame "Hv".
    by iApply "Hsub".
  Qed.

  Lemma Fld_Sub_Fld' {Γ T1 T2 i j l}:
    Γ ⊨ T1, i <: T2, j + i -∗ Γ ⊨ TVMem l T1, i <: TVMem l T2, j + i.
  Proof. apply sFld_Sub_Fld'. Qed.

  Lemma Fld_Sub_Fld {Γ T1 T2 i l}:
    Γ ⊨ T1, i <: T2, i -∗ Γ ⊨ TVMem l T1, i <: TVMem l T2, i.
  Proof. iApply (Fld_Sub_Fld' (j := 0)). Qed.

  Lemma sAll_Sub_All {Γ T1 T2 U1 U2 i} `{!SwapPropI Σ} :
    Γ s⊨ oLater T2, i <: oLater T1, i -∗
    oLaterN (S i) (shift T2) :: Γ s⊨ oLater U1, i <: oLater U2, i -∗
    Γ s⊨ oAll T1 U1, i <: oAll T2 U2, i.
  Proof.
    iIntros "#HsubT #HsubU /= !> %ρ %v #Hg #HT1".
    iDestruct "HT1" as (t) "#[Heq #HT1]". iExists t; iSplit => //.
    iIntros (w).
    rewrite -!mlaterN_pers -mlaterN_impl.
    iIntros "!> #HwT2".
    iSpecialize ("HsubT" $! ρ w with "Hg HwT2").
    iSpecialize ("HsubU" $! (w .: ρ)); iEval (rewrite -forall_swap_impl) in "HsubU".
    iSpecialize ("HsubU" with "[# $Hg]").
    by rewrite -swap_later /=; iApply hoEnvD_weaken_one.
    setoid_rewrite mlaterN_impl; setoid_rewrite mlater_impl.
    iNext i; iNext 1. iModIntro. iApply wp_wand.
    - iApply ("HT1" with "[]"). iApply "HsubT".
    - iIntros (u) "#HuU1". by iApply "HsubU".
  Qed.

  Lemma All_Sub_All {Γ} T1 T2 U1 U2 i `{!SwapPropI Σ} :
    Γ ⊨ TLater T2, i <: TLater T1, i -∗
    iterate TLater (S i) (shift T2) :: Γ ⊨ TLater U1, i <: TLater U2, i -∗
    Γ ⊨ TAll T1 U1, i <: TAll T2 U2, i.
  Proof.
    rewrite /istpi fmap_cons iterate_TLater_oLater.
    rewrite (interp_subst_commute T2 (ren (+1))).
    apply sAll_Sub_All.
  Qed.

  (** ** Type members: variance of [cTMem], that is [{A :: L .. U}]. *)
  Lemma sTyp_Sub_Typ {Γ L1 L2 U1 U2 i l} `{!SwapPropI Σ} :
    Γ s⊨ oLater L2, i <: oLater L1, i -∗
    Γ s⊨ oLater U1, i <: oLater U2, i -∗
    Γ s⊨ cTMem l L1 U1, i <: cTMem l L2 U2, i.
  Proof.
    iIntros "#HL #HU !> %ρ %v #Hg #HT1".
    iDestruct "HT1" as (d) "[Hl H]".
    iDestruct "H" as (φ) "#[Hφl [HLφ #HφU]]".
    simpl. setoid_rewrite mlaterN_impl.
    iExists d; repeat iSplit; first by iNext.
    iExists φ; repeat iSplitL; first by [iNext];
      rewrite -!mlaterN_pers;
      iIntros "!>" (w);
      iSpecialize ("HL" $! ρ w with "Hg");
      iSpecialize ("HU" $! ρ w with "Hg");
      iNext i; iIntros "#H".
    - by iApply ("HLφ" with "(HL H)").
    - by iApply ("HU" with "(HφU H)").
  Qed.

  Lemma Typ_Sub_Typ {Γ L1 L2 U1 U2 i l} `{!SwapPropI Σ} :
    Γ ⊨ TLater L2, i <: TLater L1, i -∗
    Γ ⊨ TLater U1, i <: TLater U2, i -∗
    Γ ⊨ TTMem l L1 U1, i <: TTMem l L2 U2, i.
  Proof. apply sTyp_Sub_Typ. Qed.
End StpLemmas.

Section VarianceStpLemmas.
  Context `{HdotG: !dlangG Σ}.

  (* Is it true that for covariant F, F[A ∧ B] = F[A] ∧ F[B]?
    Dotty assumes that, tho DOT didn't capture it.
    F[A ∧ B] <: F[A] ∧ F[B] is provable by covariance.
    Let's prove F[A] ∧ F[B] <: F[A ∧ B] in the model.
    *)
  Lemma sAnd_All_Sub_Distr Γ T U1 U2 i:
    ⊢ Γ s⊨ oAnd (oAll T U1) (oAll T U2), i <: oAll T (oAnd U1 U2), i.
  Proof.
    iIntros "/= !> %ρ %v #Hg [#H1 #H2]". iNext.
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

  Lemma sAnd_Fld_Sub_Distr Γ l T1 T2 i:
    ⊢ Γ s⊨ oAnd (cVMem l T1) (cVMem l T2), i <: cVMem l (oAnd T1 T2), i.
  Proof.
    iIntros "/= !> %ρ %v #Hg [#H1 H2]". iNext.
    iDestruct "H1" as (d? pmem?) "#H1"; iDestruct "H2" as (d'? pmem'?) "#H2". objLookupDet.
    repeat (iExists _; repeat iSplit => //).
    by iApply (path_wp_and' with "H1 H2").
  Qed.

  Lemma sAnd_Typ_Sub_Distr Γ l L U1 U2 i:
    ⊢ Γ s⊨ oAnd (cTMem l L U1) (cTMem l L U2), i <: cTMem l L (oAnd U1 U2), i.
  Proof.
    iIntros "/= !> %ρ %v Hg [H1 H2]". iNext.
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

End VarianceStpLemmas.
