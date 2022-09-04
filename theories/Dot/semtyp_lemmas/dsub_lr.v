(** * Semantic lemmas for single-delay subtyping. *)
From iris.proofmode Require Import proofmode.

From D Require Import iris_prelude swap_later_impl.
From D.Dot Require Import dot_semtypes.

Implicit Types (Σ : gFunctors).
Implicit Types (v : vl) (e : tm) (d : dm) (ds : dms) (ρ : env) (l : label).

Set Suggest Proof Using.
Set Implicit Arguments.
Unset Strict Implicit.

Section DStpLemmas.
  Context `{HdotG : !dlangG Σ} `{!RecTyInterp Σ}.

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
  Proof. iIntros "!> %ρ _ !>"; by rewrite -subtype_refl. Qed.

  Lemma sStp_Trans {Γ T1 T2 T3 i} :
    Γ s⊨ T1 <:[i] T2 -∗ Γ s⊨ T2 <:[i] T3 -∗ Γ s⊨ T1 <:[i] T3.
  Proof.
    iIntros ">#Hsub1 >#Hsub2 !> %ρ #Hg *".
    iApply (subtype_trans with "(Hsub1 Hg) (Hsub2 Hg)").
  Qed.

  Lemma sStp_Top Γ T i :
    ⊢ Γ s⊨ T <:[i] oTop.
  Proof. rewrite sstpd_eq_1. by iIntros "!> ** !> **". Qed.

  Lemma sBot_Stp Γ T i :
    ⊢ Γ s⊨ oBot <:[i] T.
  Proof. rewrite sstpd_eq_1. by iIntros "!> /= ** !> []". Qed.

  Lemma sAnd1_Stp Γ T1 T2 i :
    ⊢ Γ s⊨ oAnd T1 T2 <:[i] T1.
  Proof. rewrite sstpd_eq. by iIntros "!> /= %ρ %v _ !> [$ _]". Qed.
  Lemma sAnd2_Stp Γ T1 T2 i :
    ⊢ Γ s⊨ oAnd T1 T2 <:[i] T2.
  Proof. rewrite sstpd_eq. by iIntros "!> /= %ρ %v _ !> [_ $]". Qed.

  Lemma sStp_And Γ T U1 U2 i :
    Γ s⊨ T <:[i] U1 -∗
    Γ s⊨ T <:[i] U2 -∗
    Γ s⊨ T <:[i] oAnd U1 U2.
  Proof.
    rewrite !sstpd_eq; iIntros ">#H1 >#H2 !> %ρ %v #Hg".
    iSpecialize ("H1" $! ρ v with "Hg"); iSpecialize ("H2" $! ρ v with "Hg").
    iNext i; iIntros "#H".
    iSplit; [iApply "H1" | iApply "H2"]; iApply "H".
  Qed.

  Lemma sStp_Or1 Γ T1 T2 i : ⊢ Γ s⊨ T1 <:[i] oOr T1 T2.
  Proof. rewrite sstpd_eq. by iIntros "!> /= %ρ %v _ !>"; eauto. Qed.
  Lemma sStp_Or2 Γ T1 T2 i : ⊢ Γ s⊨ T2 <:[i] oOr T1 T2.
  Proof. rewrite sstpd_eq. by iIntros "!> /= %ρ %v _ !>"; eauto. Qed.

  Lemma sOr_Stp Γ T1 T2 U i :
    Γ s⊨ T1 <:[i] U -∗
    Γ s⊨ T2 <:[i] U -∗
    Γ s⊨ oOr T1 T2 <:[i] U.
  Proof.
    rewrite !sstpd_eq; iIntros ">#H1 >#H2 !> * #Hg".
    iSpecialize ("H1" $! ρ v with "Hg"); iSpecialize ("H2" $! ρ v with "Hg").
    iNext i; iIntros "#[HT | HT]"; [iApply "H1" | iApply "H2"]; iApply "HT".
  Qed.

  Lemma sDistr_And_Or_Stp Γ {S T U i} : ⊢ Γ s⊨ oAnd (oOr S T) U <:[i] oOr (oAnd S U) (oAnd T U).
  Proof.
    rewrite sstpd_eq.
    by iIntros "!> %ρ %v #Hg !> [[HS|HT] Hu] /="; [iLeft|iRight]; iFrame.
  Qed.

  (* XXX must we state the two separate halves? *)
  Lemma sLater_Stp_Eq {Γ T U i} `{SwapPropI Σ} :
    Γ s⊨ T <:[i.+1] U ⊣⊢
    Γ s⊨ oLater T <:[i] oLater U.
  Proof. by rewrite sstpd_delay_oLaterN_plus. Qed.

  Lemma sStp_Add_LaterN {Γ T i j} :
    ⊢ Γ s⊨ T <:[i] oLaterN j T.
  Proof. rewrite sstpd_eq; iIntros "!> ** !> $".  Qed.
  Lemma sStp_Add_Later {Γ T i} :
    ⊢ Γ s⊨ T <:[i] oLater T.
  Proof. apply sStp_Add_LaterN. Qed.

  Lemma sStp_Sel {Γ L U p l i} :
    Γ s⊨p p : oTMem l L U, i -∗
    Γ s⊨ L <:[i] oSel p l.
  Proof.
    rewrite sstpd_eq; iIntros ">#Hp !> %ρ %v Hg".
    iSpecialize ("Hp" with "Hg"); iNext i; iIntros "#HL".
    iApply (path_wp_wand with "Hp"); iIntros (w).
    iApply (vl_sel_lb with "HL").
  Qed.

  Lemma sSel_Stp {Γ L U p l i} :
    Γ s⊨p p : oTMem l L U, i -∗
    Γ s⊨ oSel p l <:[i] U.
  Proof.
    rewrite sstpd_eq; iIntros ">#Hp !> %ρ %v Hg".
    iSpecialize ("Hp" with "Hg"); iNext i; iIntros "Hφ".
    iDestruct (path_wp_agree with "Hp Hφ") as (w Hw) "[Hp Hφ]".
    iApply (vl_sel_ub with "Hφ Hp").
  Qed.

  (*
     Γ, z : T₁ᶻ ⊨ T₁ᶻ <: T₂ᶻ
     ----------------------------------------------- (μ-<:-μ)
     Γ ⊨ μ (x : T₁ˣ) <: μ(x : T₂ˣ)
  *)
  Lemma sMu_Stp_Mu {Γ T1 T2 i} `{!SwapPropI Σ} :
    oLaterN i T1 :: Γ s⊨ T1 <:[i] T2 -∗
    Γ s⊨ oMu T1 <:[i] oMu T2.
  Proof.
    rewrite !sstpd_eq; iIntros ">#Hstp !> %ρ %v Hg".
    iApply mlaterN_impl; iIntros "#HT1".
    iApply ("Hstp" $! (v .: ρ) v with "[$Hg $HT1] HT1").
  Qed.

  (**
  Novel subtyping rules for recursive types:
     x ∉ fv T
     -----------------------------------------------
     Γ ⊨ mu x : T <: T    Γ ⊨ T <: mu(x : T)

  [Stp_Bind_1] and [Stp_Bind_2] become derivable. *)
  Lemma sMu_Stp {Γ T i} : ⊢ Γ s⊨ oMu (shift T) <:[i] T.
  Proof. rewrite oMu_shift. apply sStp_Refl. Qed.

  Lemma sStp_Mu {Γ T i} : ⊢ Γ s⊨ T <:[i] oMu (shift T).
  Proof. rewrite oMu_shift. apply sStp_Refl. Qed.

  Lemma sFld_Stp_Fld {Γ T1 T2 i l} :
    Γ s⊨ T1 <:[i] T2 -∗
    Γ s⊨ oVMem l T1 <:[i] oVMem l T2.
  Proof.
    iIntros ">#Hsub !> %ρ Hg"; iSpecialize ("Hsub" with "Hg"); iNext i.
    iApply (oVMem_respects_sub with "Hsub").
  Qed.

  Lemma sTyp_Stp_Typ Γ L1 L2 U1 U2 i l :
    Γ s⊨ L2 <:[i] L1 -∗
    Γ s⊨ U1 <:[i] U2 -∗
    Γ s⊨ oTMem l L1 U1 <:[i] oTMem l L2 U2.
  Proof.
    iIntros ">#HsubL >#HsubU !> %ρ #Hg".
    iSpecialize ("HsubL" with "Hg"); iSpecialize ("HsubU" with "Hg"); iNext i.
    iApply (oTMem_respects_sub with "HsubL HsubU").
  Qed.

  Lemma sAll_Stp_All Γ T1 T2 U1 U2 i `{!SwapPropI Σ} :
    Γ s⊨ oLater T2 <:[i] oLater T1 -∗
    oLaterN (i.+1) (oShift T2) :: Γ s⊨ oLater U1 <:[i] oLater U2 -∗
    Γ s⊨ oAll T1 U1 <:[i] oAll T2 U2.
  Proof.
    rewrite !sstpd_delay_oLaterN_plus; iIntros ">#HsubT >#HsubU !> %ρ #Hg %v".
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

  (* An inverse of subsumption: subtyping is *equivalent* to convertibility
  for values. *)

  Lemma sStp_Skolem_P {Γ T1 T2 i j} `{!SwapPropI Σ} :
    oLaterN i (shift T1) :: Γ s⊨p pv (ids 0) : shift T2, i + j -∗
    (*───────────────────────────────*)
    Γ s⊨ T1 <:[i] oLaterN j T2.
  Proof.
    rewrite -sstpd_delay_oLaterN; iIntros ">#Htyp !> %ρ Hg %v HvT1".
    iEval rewrite /= -(path_wp_pv_eq _ (T2 _ _)) -laterN_plus.
    iApply ("Htyp" $! (v .: ρ) with "[$Hg $HvT1]").
  Qed.

  (* Is it true that for covariant F, F[A ∧ B] = F[A] ∧ F[B]?
    Dotty assumes that, tho DOT didn't capture it.
    F[A ∧ B] <: F[A] ∧ F[B] is provable by covariance.
    Let's prove F[A] ∧ F[B] <: F[A ∧ B] in the model.
    *)
  Lemma sAnd_All_1_Stp_Distr Γ S T1 T2 i :
    ⊢ Γ s⊨ oAnd (oAll S T1) (oAll S T2) <:[i] oAll S (oAnd T1 T2).
  Proof.
    iIntros "!> %ρ _ !> %v [#H1 #H2]".
    iDestruct "H1" as (t ?) "#H1"; iDestruct "H2" as (t' ->) "#H2"; simplify_eq.
    iExists t; iSplit; first done.
    iIntros (w) "#HS".
    (* Oh. Dreaded conjunction rule. Tho could we use a version
    for separating conjunction? *)
    iApply (wp_and with "(H1 HS) (H2 HS)").
  Qed.

  Lemma sAnd_All_2_Stp_Distr Γ S1 S2 T i :
    ⊢ Γ s⊨ oAnd (oAll S1 T) (oAll S2 T) <:[i] oAll (oOr S1 S2) T.
  Proof.
    iIntros "!> %ρ _ !> %v [#H1 #H2]".
    iDestruct "H1" as (t ?) "#H1"; iDestruct "H2" as (t' ->) "#H2"; simplify_eq.
    iExists t; iSplit; first done.
    iIntros (w) "#[HS|HS]"; [iApply ("H1" with "HS")|iApply ("H2" with "HS")].
  Qed.

  (**
    We cannot combine the two rules to get
    [⊢ Γ s⊨ oAnd (oAll S1 T1) (oAll S2 T2) <:[i] oAll (oOr S1 S2) (oAnd T1 T2)].

    Counterexample:
    [id : Int -> Int] and [id : String -> String], but not [id : Int \/ String -> Int /\ String)].
  *)

  Lemma sAnd_Fld_Stp_Distr Γ l T1 T2 i :
    ⊢ Γ s⊨ oAnd (oVMem l T1) (oVMem l T2) <:[i] oVMem l (oAnd T1 T2).
  Proof.
    iIntros "!> %ρ _ !> %v [#H1 H2]"; rewrite !oVMem_eq.
    iDestruct "H1" as (pmem Hl) "#H1"; iDestruct "H2" as (pmem' Hl') "#H2".
    objLookupDet. iExists pmem; iFrame (Hl).
    by iApply (path_wp_and' with "H1 H2").
  Qed.

  Lemma sAnd_Typ_Stp_Distr Γ l L1 L2 U1 U2 i :
    ⊢ Γ s⊨ oAnd (oTMem l L1 U1) (oTMem l L2 U2) <:[i] oTMem l (oOr L1 L2) (oAnd U1 U2).
  Proof.
    iIntros "!> %ρ _ !> %v [H1 H2]"; rewrite !oTMem_eq /dot_intv_type_pred.
    iDestruct "H1" as (ψ d Hl) "[Hdψ1 [HLψ1 HψU1]]".
    iDestruct "H2" as (ψ' d' Hl') "[Hdψ2 [HLψ2 HψU2]]". objLookupDet.
    iExists ψ, d. iFrame (Hl). iSplit; first done.
    iSplit; iIntros (w) "Hw";
      iDestruct (dm_to_type_agree anil w with "Hdψ1 Hdψ2") as "Hag".
    - iDestruct "Hw" as "[Hw|Hw]"; first iApply ("HLψ1" with "Hw").
      iSpecialize ("HLψ2" with "Hw").
      iNext. by iRewrite "Hag".
    - iSplit; [iApply ("HψU1" with "Hw") | iApply "HψU2"].
      iNext. by iRewrite -"Hag".
  Qed.

  Lemma sOr_Fld_Stp_Distr Γ l T1 T2 i :
    ⊢ Γ s⊨ oVMem l (oOr T1 T2) <:[i] oOr (oVMem l T1) (oVMem l T2).
  Proof.
    iIntros "!> %ρ _ !> %v". rewrite !oVMem_eq.
    iDestruct 1 as (pmem Hl) "Hp". rewrite path_wp_eq.
    iDestruct "Hp" as (w Hpw) "[H|H]"; [iLeft|iRight].
    all: by rewrite oVMem_eq; iExists (pmem); iFrame (Hl);
      rewrite path_wp_eq; iExists (w); iFrame (Hpw).
  Qed.

  (**
  Most dual rules for union types do not actually hold.
  In fact, even [sOr_Fld_Stp_Distr] is subtle, and only works in CBV
  semantics.

  For more on the trickiness of union types in general, see the introduction
  of [Subtyping for union types]
  (https://link.springer.com/chapter/10.1007/978-3-540-30124-0_32) (also [on
  Citeseer](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.60.6019&rep=rep1&type=pdf)).

  Specific cases follow.

  There is no union rule for type members (except the derivable ones).
  Symmetry suggests the following rule, which however is incorrect:
    [⊢ Γ s⊨ oTMem l (oAnd L1 L2) (oOr U1 U2) <:[i] oOr (oTMem l L1 U1) (oTMem l L2 U2)].
  Here are weaker rules, with counterexamples:
  - [⊢ Γ s⊨ oTMem l L (oOr U1 U2) <:[i] oOr (oTMem l L U1) (oTMem l L U2)]:
    Ignoring laters, the witness (actual rhs of the type member) can be [U1 ∨
    U2], which is a subtype of [U1 ∨ U2], but not of [U1], and not of [U2].
    In particular, we can have [U1 ∨ U2 = ⊤].
  - [⊢ Γ s⊨ oTMem l (oAnd L1 L2) U <:[i] oOr (oTMem l L1 U) (oTMem l L2 U)]:
    Again, ignoring laters, the witness can be [L1 ∧ L2], which isn't a supertype of [L1] or [L2].
    In particular, we can have [L1 ∧ L2 = ⊥].

  There is also no union rule for function types (except the derivable ones).
  - [⊢ Γ s⊨ oAll S (oOr T1 T2) <:[i] oOr (oAll S T1) (oAll S T2)]:
    For instance, we can give an [f] such that
    [f: Int -> Int ∨ String], but not [f: (Int -> Int) \/ (Int -> String)].
    It's sufficient that [f] returns an [Int] on some inputs (say, [0]) and a
    [String] on others (say, [1]).
  *)

  Lemma sP_Later {Γ} p T i :
    Γ s⊨p p : oLater T, i -∗
    Γ s⊨p p : T, i.+1.
  Proof.
    iIntros ">#HpT !> %ρ #Hg"; rewrite -later_laterN laterN_later.
    iSpecialize ("HpT" with "Hg"); iNext i.
    iApply (path_wp_later_swap with "HpT").
  Qed.
End DStpLemmas.
