(** * Semantic lemmas for single-delay subtyping. *)
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

From D Require Import iris_prelude swap_later_impl.
From D.Dot Require Import unary_lr.

Implicit Types (Σ : gFunctors).
Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms) (ρ : env) (l : label).

Set Suggest Proof Using.
Set Default Proof Using "Type*".
Set Implicit Arguments.
Unset Strict Implicit.

Section DStpLemmas.
  Context `{HdotG: !dlangG Σ}.

  Lemma sstpd_delay_oLaterN `{!SwapPropI Σ} Γ i T1 T2 :
    Γ s⊨ oLaterN i T1 <:[0] oLaterN i T2 ⊣⊢
    Γ s⊨ T1 <:[i] T2.
  Proof.
    rewrite !sstpd_eq_1 /subtype_lty /=; properness; first done.
    by rewrite mlaterN_impl.
  Qed.

  Lemma sstpd_delay_oLaterN_plus `{!SwapPropI Σ} Γ i j T1 T2 :
    Γ s⊨ oLaterN i T1 <:[j] oLaterN i T2 ⊣⊢
    Γ s⊨ T1 <:[i+j] T2.
  Proof.
    by rewrite -sstpd_delay_oLaterN -!oLaterN_plus (Nat.add_comm i j)
      sstpd_delay_oLaterN.
  Qed.


  Lemma sStp_Refl {Γ} T i : ⊢ Γ s⊨ T <:[i] T.
  Proof. iIntros "%ρ _ !>"; by rewrite -subtype_refl. Qed.

  Lemma sStp_Trans {Γ T1 T2 T3 i} :
    Γ s⊨ T1 <:[i] T2 -∗ Γ s⊨ T2 <:[i] T3 -∗ Γ s⊨ T1 <:[i] T3.
  Proof.
    iIntros "#Hsub1 #Hsub2 %ρ #Hg *".
    iApply (subtype_trans with "(Hsub1 Hg) (Hsub2 Hg)").
  Qed.

  Lemma sStp_Top Γ T i:
    ⊢ Γ s⊨ T <:[i] oTop.
  Proof. rewrite sstpd_eq_1. by iIntros "** !> ** /=". Qed.

  Lemma sBot_Stp Γ T i:
    ⊢ Γ s⊨ oBot <:[i] T.
  Proof. rewrite sstpd_eq_1. by iIntros "/= ** !> []". Qed.

  Lemma sAnd1_Stp Γ T1 T2 i :
    ⊢ Γ s⊨ oAnd T1 T2 <:[i] T1.
  Proof. rewrite sstpd_eq. by iIntros "/= %ρ %v _ !> [$ _]". Qed.
  Lemma sAnd2_Stp Γ T1 T2 i :
    ⊢ Γ s⊨ oAnd T1 T2 <:[i] T2.
  Proof. rewrite sstpd_eq. by iIntros "/= %ρ %v _ !> [_ $]". Qed.

  Lemma sStp_And Γ T U1 U2 i:
    Γ s⊨ T <:[i] U1 -∗
    Γ s⊨ T <:[i] U2 -∗
    Γ s⊨ T <:[i] oAnd U1 U2.
  Proof.
    rewrite !sstpd_eq; iIntros "#H1 #H2 %ρ %v #Hg".
    iSpecialize ("H1" $! ρ v with "Hg"); iSpecialize ("H2" $! ρ v with "Hg").
    iNext i; iIntros "#H".
    iSplit; [iApply "H1" | iApply "H2"]; iApply "H".
  Qed.

  Lemma sStp_Or1 Γ T1 T2 i: ⊢ Γ s⊨ T1 <:[i] oOr T1 T2.
  Proof. rewrite sstpd_eq. by iIntros "/= %ρ %v _ !>"; eauto. Qed.
  Lemma sStp_Or2 Γ T1 T2 i: ⊢ Γ s⊨ T2 <:[i] oOr T1 T2.
  Proof. rewrite sstpd_eq. by iIntros "/= %ρ %v _ !>"; eauto. Qed.

  Lemma sOr_Stp Γ T1 T2 U i:
    Γ s⊨ T1 <:[i] U -∗
    Γ s⊨ T2 <:[i] U -∗
    Γ s⊨ oOr T1 T2 <:[i] U.
  Proof.
    rewrite !sstpd_eq; iIntros "/= #H1 #H2 * #Hg".
    iSpecialize ("H1" $! ρ v with "Hg"); iSpecialize ("H2" $! ρ v with "Hg").
    iNext i; iIntros "#[HT | HT]"; [iApply "H1" | iApply "H2"]; iApply "HT".
  Qed.

  Lemma sDistr_And_Or_Stp Γ {S T U i} : ⊢ Γ s⊨ oAnd (oOr S T) U <:[i] oOr (oAnd S U) (oAnd T U).
  Proof.
    rewrite sstpd_eq.
    by iIntros "%ρ %v #Hg !> [[HS|HT] Hu] /="; [iLeft|iRight]; iFrame.
  Qed.

  (* XXX must we state the two separate halves? *)
  Lemma sLater_Stp_Eq {Γ T U i} `{SwapPropI Σ}:
    Γ s⊨ T <:[i.+1] U ⊣⊢
    Γ s⊨ oLater T <:[i] oLater U.
  Proof. by rewrite sstpd_delay_oLaterN_plus. Qed.

  Lemma sStp_Add_LaterN {Γ T i j}:
    ⊢ Γ s⊨ T <:[i] oLaterN j T.
  Proof. rewrite sstpd_eq; iIntros "** !> $".  Qed.
  Lemma sStp_Add_Later {Γ T i}:
    ⊢ Γ s⊨ T <:[i] oLater T.
  Proof. apply sStp_Add_LaterN. Qed.

  Lemma sStp_Sel {Γ L U p l i}:
    Γ s⊨p p : oTMem l L U, i -∗
    Γ s⊨ L <:[i] oSel p l.
  Proof.
    rewrite sstpd_eq; iIntros "#Hp %ρ %v Hg".
    iSpecialize ("Hp" with "Hg"); iNext i; iIntros "#HL".
    iApply (path_wp_wand with "Hp"); iIntros (w).
    iApply (vl_sel_lb with "HL").
  Qed.

  Lemma sSel_Stp {Γ L U p l i}:
    Γ s⊨p p : oTMem l L U, i -∗
    Γ s⊨ oSel p l <:[i] U.
  Proof.
    rewrite sstpd_eq; iIntros "#Hp %ρ %v Hg".
    iSpecialize ("Hp" with "Hg"); iNext i; iIntros "Hφ".
    iDestruct (path_wp_agree with "Hp Hφ") as (w Hw) "[Hp Hφ]".
    iApply (vl_sel_ub with "Hφ Hp").
  Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂ᶻ
     ----------------------------------------------- (μ-<:-μ)
     Γ ⊨ μ (x: T₁ˣ) <: μ(x: T₂ˣ)
  *)
  Lemma sMu_Stp_Mu {Γ T1 T2 i} `{!SwapPropI Σ}:
    oLaterN i T1 :: Γ s⊨ T1 <:[i] T2 -∗
    Γ s⊨ oMu T1 <:[i] oMu T2.
  Proof.
    rewrite !sstpd_eq; iIntros "/= #Hstp %ρ %v Hg".
    iApply mlaterN_impl; iIntros "#HT1".
    iApply ("Hstp" $! (v .: ρ) v with "[$Hg $HT1] [$HT1]").
  Qed.

  Lemma Mu_Stp_Mu {Γ} T1 T2 i `{!SwapPropI Σ}:
    iterate TLater i T1 :: Γ ⊨ T1 <:[i] T2 -∗
    Γ ⊨ TMu T1 <:[i] TMu T2.
  Proof.
    rewrite /istpd -sMu_Stp_Mu.
    by rewrite fmap_cons (iterate_TLater_oLater i T1).
  Qed.

  (**
  Novel subtyping rules for recursive types:
     x ∉ fv T
     -----------------------------------------------
     Γ ⊨ mu x: T <: T    Γ ⊨ T <: mu(x: T)

  [Stp_Bind_1] and [Stp_Bind_2] become derivable. *)
  Lemma sMu_Stp {Γ T i} : ⊢ Γ s⊨ oMu (shift T) <:[i] T.
  Proof. rewrite oMu_shift. apply sStp_Refl. Qed.

  Lemma Mu_Stp {Γ} T i: ⊢ Γ ⊨ TMu (shift T) <:[i] T.
  Proof.
    rewrite /istpd; cbn -[sstpd].
    rewrite (interp_subst_commute T (ren (+1))).
    apply sMu_Stp.
  Qed.

  Lemma sStp_Mu {Γ T i} : ⊢ Γ s⊨ T <:[i] oMu (shift T).
  Proof. rewrite oMu_shift. apply sStp_Refl. Qed.

  Lemma Stp_Mu {Γ} T i: ⊢ Γ ⊨ T <:[i] TMu (shift T).
  Proof.
    rewrite /istpd; cbn -[sstpd].
    rewrite (interp_subst_commute T (ren (+1))).
    apply sStp_Mu.
  Qed.

  Lemma sFld_Stp_Fld {Γ T1 T2 i l}:
    Γ s⊨ T1 <:[i] T2 -∗
    Γ s⊨ oVMem l T1 <:[i] oVMem l T2.
  Proof.
    iIntros "#Hsub %ρ Hg"; iSpecialize ("Hsub" with "Hg"); iNext i.
    iApply (oVMem_respects_sub with "Hsub").
  Qed.

  Lemma sTyp_Stp_Typ Γ L1 L2 U1 U2 i l :
    Γ s⊨ L2 <:[i] L1 -∗
    Γ s⊨ U1 <:[i] U2 -∗
    Γ s⊨ oTMem l L1 U1 <:[i] oTMem l L2 U2.
  Proof.
    iIntros "#HsubL #HsubU %ρ #Hg".
    iSpecialize ("HsubL" with "Hg"); iSpecialize ("HsubU" with "Hg"); iNext i.
    iApply (oTMem_respects_sub with "HsubL HsubU").
  Qed.

  Lemma sAll_Stp_All Γ T1 T2 U1 U2 i `{!SwapPropI Σ}:
    Γ s⊨ oLater T2 <:[i] oLater T1 -∗
    oLaterN (i.+1) (oShift T2) :: Γ s⊨ oLater U1 <:[i] oLater U2 -∗
    Γ s⊨ oAll T1 U1 <:[i] oAll T2 U2.
  Proof.
    rewrite !sstpd_delay_oLaterN_plus; iIntros "#HsubT #HsubU %ρ #Hg %v".
    rewrite -!mlaterN_impl.
    iDestruct 1 as (t) "#[Heq #HT1]"; iExists t; iFrame "Heq".
    iIntros (w); iSpecialize ("HT1" $! w).
    rewrite -!mlaterN_impl -!laterN_later.
    iIntros "#HwT2".
    iSpecialize ("HsubT" with "Hg").
    iSpecialize ("HsubU" $! (w .: ρ) with "[$HwT2 $Hg]").
    rewrite !mlaterN_impl.
    iNext (i.+1). wp_wapply "(HT1 (HsubT HwT2))".
    iIntros (u) "#HuU1". iApply ("HsubU" with "HuU1").
  Qed.

  Lemma All_Stp_All {Γ} T1 T2 U1 U2 i `{!SwapPropI Σ}:
    Γ ⊨ TLater T2 <:[i] TLater T1 -∗
    iterate TLater i.+1 (shift T2) :: Γ ⊨ TLater U1 <:[i] TLater U2 -∗
    Γ ⊨ TAll T1 U1 <:[i] TAll T2 U2.
  Proof.
    rewrite /istpd fmap_cons iterate_TLater_oLater.
    rewrite (interp_subst_commute T2 (ren (+1))).
    apply: sAll_Stp_All.
  Qed.

  (* An inverse of subsumption: subtyping is *equivalent* to convertibility
  for values. *)

  Lemma sStp_Skolem_P {Γ T1 T2 i j} `{!SwapPropI Σ} :
    oLaterN i (shift T1) :: Γ s⊨p pv (ids 0) : shift T2, i + j -∗
    (*───────────────────────────────*)
    Γ s⊨ T1 <:[i] oLaterN j T2.
  Proof.
    rewrite -sstpd_delay_oLaterN; iIntros "#Htyp %ρ Hg %v HvT1".
    iEval rewrite /= -(path_wp_pv_eq _ (T2 _ _)) -laterN_plus.
    iApply ("Htyp" $! (v .: ρ) with "[$Hg $HvT1]").
  Qed.

  Lemma Stp_Skolem_P {Γ T1 T2 i j} `{!SwapPropI Σ} :
    iterate TLater i (shift T1) :: Γ ⊨p pv (ids 0) : shift T2, i + j -∗
    (*───────────────────────────────*)
    Γ ⊨ T1 <:[i] iterate TLater j T2.
  Proof.
    rewrite /iptp /istpd fmap_cons !iterate_TLater_oLater !interp_subst_commute.
    exact: sStp_Skolem_P.
  Qed.

  (* Is it true that for covariant F, F[A ∧ B] = F[A] ∧ F[B]?
    Dotty assumes that, tho DOT didn't capture it.
    F[A ∧ B] <: F[A] ∧ F[B] is provable by covariance.
    Let's prove F[A] ∧ F[B] <: F[A ∧ B] in the model.
    *)
  Lemma sAnd_All_Stp_Distr Γ T U1 U2 i:
    ⊢ Γ s⊨ oAnd (oAll T U1) (oAll T U2) <:[i] oAll T (oAnd U1 U2).
  Proof.
    iIntros "%ρ _ !> %v [#H1 #H2]".
    iDestruct "H1" as (t ?) "#H1"; iDestruct "H2" as (t' ->) "#H2"; simplify_eq.
    iExists t; iSplit; first done.
    iIntros (w) "#HT".
    (* Oh. Dreaded conjunction rule. Tho could we use a version
    for separating conjunction? *)
    iApply (wp_and with "(H1 HT) (H2 HT)").
  Qed.

  Lemma sAnd_Fld_Stp_Distr Γ l T1 T2 i:
    ⊢ Γ s⊨ oAnd (oVMem l T1) (oVMem l T2) <:[i] oVMem l (oAnd T1 T2).
  Proof.
    iIntros "%ρ _ !> %v [#H1 H2]"; rewrite !oVMem_eq.
    iDestruct "H1" as (pmem Hl) "#H1"; iDestruct "H2" as (pmem' Hl') "#H2".
    objLookupDet. iExists pmem; iFrame (Hl).
    by iApply (path_wp_and' with "H1 H2").
  Qed.

  Lemma sAnd_Typ_Stp_Distr Γ l L U1 U2 i:
    ⊢ Γ s⊨ oAnd (oTMem l L U1) (oTMem l L U2) <:[i] oTMem l L (oAnd U1 U2).
  Proof.
    iIntros "%ρ _ !> %v [H1 H2]"; rewrite !oTMem_eq /dot_intv_type_pred.
    iDestruct "H1" as (ψ d Hl) "[Hdψ1 [HLψ1 HψU1]]".
    iDestruct "H2" as (ψ' d' Hl') "[Hdψ2 [_ HψU2]]". objLookupDet.
    iExists ψ, d. iFrame (Hl) "HLψ1". iSplit; first done.
    iIntros (w) "Hw".
    iDestruct (dm_to_type_agree vnil w with "Hdψ1 Hdψ2") as "Hag".
    iSplit; [iApply ("HψU1" with "Hw") | iApply "HψU2"].
    iNext. by iRewrite -"Hag".
  Qed.

  Lemma sOr_Fld_Stp_Distr Γ l T1 T2 i:
    ⊢ Γ s⊨ oVMem l (oOr T1 T2) <:[i] oOr (oVMem l T1) (oVMem l T2).
  Proof.
    iIntros "%ρ _ !> %v". rewrite !oVMem_eq.
    iDestruct 1 as (pmem Hl) "Hp". rewrite path_wp_eq.
    iDestruct "Hp" as (w Hpw) "[H|H]"; [iLeft|iRight].
    all: by rewrite oVMem_eq; iExists (pmem); iFrame (Hl);
      rewrite path_wp_eq; iExists (w); iFrame (Hpw).
  Qed.


  Lemma sP_Later {Γ} p T i :
    Γ s⊨p p : oLater T, i -∗
    Γ s⊨p p : T, i.+1.
  Proof.
    iIntros "#HpT %ρ #Hg"; rewrite -later_laterN laterN_later.
    iSpecialize ("HpT" with "Hg"); iNext i.
    iApply (path_wp_later_swap with "HpT").
  Qed.
End DStpLemmas.
