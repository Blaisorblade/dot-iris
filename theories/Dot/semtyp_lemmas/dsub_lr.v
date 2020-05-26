(** * Semantic lemmas for single-delay subtyping. *)
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

From D Require Import iris_prelude succ_notation swap_later_impl proper.
From D.Dot Require Import rules path_repl unary_lr defs_lr.

Implicit Types (Σ : gFunctors).
Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms) (ρ : env) (l : label).

Set Suggest Proof Using.
Set Default Proof Using "Type*".
Set Implicit Arguments.
Unset Strict Implicit.

Section defs.
  Context {Σ}.
  Implicit Types (τ : oltyO Σ 0).
  (** Delayed subtyping. *)
  Definition sstpd `{!dlangG Σ} i Γ τ1 τ2 : iProp Σ :=
    □∀ ρ,
      sG⟦Γ⟧*ρ → ▷^i (oClose τ1 ρ ⊆ oClose τ2 ρ).
  Global Arguments sstpd : simpl never.
  Context `{!dlangG Σ}.
  Definition istpd i Γ T1 T2 := sstpd i V⟦Γ⟧* V⟦T1⟧ V⟦T2⟧.
  (* Avoid auto-dropping box (and unfolding) when introducing judgments persistently. *)
  Local Notation IntoPersistent' P := (IntoPersistent false P P).
  Global Instance sstpd_persistent : IntoPersistent' (sstpd i Γ T1 T2) | 0 := _.
End defs.

Notation "Γ s⊨ T1 <:[ i  ] T2 " := (sstpd i Γ T1 T2) (at level 74, T1, T2 at next level).
Notation "Γ ⊨ T1 <:[ i  ] T2 " := (istpd i Γ T1 T2) (at level 74, T1, T2 at next level).
Import stamp_transfer.
Notation "Γ ⊨[ gφ  ] T1 <:[ i  ] T2 " := (wellMappedφ gφ → istpd i Γ T1 T2)%I (at level 74, T1, T2, i at next level).

(** Show these typing judgments are equivalent to what we present in the paper. *)
Section JudgDefs.
  Context `{HdotG: !dlangG Σ}.

  Lemma sstpd_eq Γ T1 i T2 :
    Γ s⊨ T1 <:[i] T2 ⊣⊢
    □∀ ρ, sG⟦Γ⟧* ρ → ∀ v, ▷^i (T1 vnil ρ v → T2 vnil ρ v).
  Proof.
    rewrite /sstpd /subtype_lty -!forall_intuitionistically; f_equiv => ρ.
    by rewrite laterN_forall.
  Qed.

  Lemma sstpd_eq' Γ T1 i T2 :
    Γ s⊨ T1 <:[i] T2 ⊣⊢
    □∀ ρ v, sG⟦Γ⟧* ρ → ▷^i (T1 vnil ρ v → T2 vnil ρ v).
  Proof. rewrite sstpd_eq; properness. apply: forall_swap_impl. Qed.

  Lemma istpd_eq Γ T1 i T2 :
    Γ ⊨ T1 <:[i] T2 ⊣⊢
    □∀ ρ, G⟦Γ⟧ ρ → ∀ v, ▷^i (V⟦T1⟧ vnil ρ v → V⟦T2⟧ vnil ρ v).
  Proof. apply sstpd_eq. Qed.

End JudgDefs.

(** * Proper instances. *)
Section Propers.
  Context `{HdotG: !dlangG Σ}.
  Implicit Types (τ L T U : olty Σ 0).

  Global Instance sstpd_proper i : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (sstpd i).
  Proof.
    solve_proper_ho.
    (* intros ?? HG ?? H1 ?? H2; rewrite /sstpd /subtype_lty;
    properness; [by rewrite HG|apply H1|apply H2]. *)
  Qed.
  Global Instance sstpd_flip_proper i :
    Proper ((≡) --> (≡) --> (≡) --> flip (≡)) (sstpd i).
  Proof. apply: flip_proper_4. Qed.
  Global Instance: Params (@sstpd) 3 := {}.
End Propers.

Section DStpLemmas.
  Context `{HdotG: !dlangG Σ}.

  Lemma sstpd_delay_oLaterN `{!SwapPropI Σ} Γ i T1 T2 :
    Γ s⊨ oLaterN i T1 <:[0] oLaterN i T2 ⊣⊢
    Γ s⊨ T1 <:[i] T2.
  Proof.
    rewrite !sstpd_eq /subtype_lty /=; properness; first done.
    by rewrite mlaterN_impl.
  Qed.

  Lemma sstpd_delay_oLaterN_plus `{!SwapPropI Σ} Γ i j T1 T2 :
    Γ s⊨ oLaterN i T1 <:[j] oLaterN i T2 ⊣⊢
    Γ s⊨ T1 <:[i+j] T2.
  Proof.
    by rewrite -sstpd_delay_oLaterN -!oLaterN_plus !(comm plus i j)
      sstpd_delay_oLaterN.
  Qed.


  Lemma sStp_Refl {Γ} T i : ⊢ Γ s⊨ T <:[i] T.
  Proof. iIntros "!> %ρ _ !>"; by rewrite -subtype_refl. Qed.

  Lemma sStp_Trans {Γ T1 T2 T3 i} : Γ s⊨ T1 <:[i] T2 -∗
                                    Γ s⊨ T2 <:[i] T3 -∗
                                    Γ s⊨ T1 <:[i] T3.
  Proof.
    iIntros "#Hsub1 #Hsub2 !> * #Hg *".
    iApply (subtype_trans with "(Hsub1 Hg) (Hsub2 Hg)").
  Qed.

  Lemma sStp_Top Γ T i:
    ⊢ Γ s⊨ T <:[i] oTop.
  Proof. rewrite sstpd_eq. by iIntros "!> ** !> ** /=". Qed.

  Lemma sBot_Stp Γ T i:
    ⊢ Γ s⊨ oBot <:[i] T.
  Proof. rewrite sstpd_eq. by iIntros "/= !> ** !> []". Qed.

  Lemma sAnd1_Stp Γ T1 T2 i :
    ⊢ Γ s⊨ oAnd T1 T2 <:[i] T1.
  Proof. rewrite sstpd_eq'. by iIntros "/= !> %ρ %v _ !> [$ _]". Qed.
  Lemma sAnd2_Stp Γ T1 T2 i :
    ⊢ Γ s⊨ oAnd T1 T2 <:[i] T2.
  Proof. rewrite sstpd_eq'. by iIntros "/= !> %ρ %v _ !> [_ $]". Qed.

  Lemma sStp_And Γ T U1 U2 i:
    Γ s⊨ T <:[i] U1 -∗
    Γ s⊨ T <:[i] U2 -∗
    Γ s⊨ T <:[i] oAnd U1 U2.
  Proof.
    rewrite !sstpd_eq'; iIntros "#H1 #H2 !> %ρ %v #Hg".
    iSpecialize ("H1" $! ρ v with "Hg"); iSpecialize ("H2" $! ρ v with "Hg").
    iNext i; iIntros "#H".
    iSplit; [iApply "H1" | iApply "H2"]; iApply "H".
  Qed.

  Lemma sStp_Or1 Γ T1 T2 i: ⊢ Γ s⊨ T1 <:[i] oOr T1 T2.
  Proof. rewrite sstpd_eq'. by iIntros "/= !> %ρ %v _ !>"; eauto. Qed.
  Lemma sStp_Or2 Γ T1 T2 i: ⊢ Γ s⊨ T2 <:[i] oOr T1 T2.
  Proof. rewrite sstpd_eq'. by iIntros "/= !> %ρ %v _ !>"; eauto. Qed.

  Lemma sOr_Stp Γ T1 T2 U i:
    Γ s⊨ T1 <:[i] U -∗
    Γ s⊨ T2 <:[i] U -∗
    Γ s⊨ oOr T1 T2 <:[i] U.
  Proof.
    rewrite !sstpd_eq'; iIntros "/= #H1 #H2 !> * #Hg".
    iSpecialize ("H1" $! ρ v with "Hg"); iSpecialize ("H2" $! ρ v with "Hg").
    iNext i; iIntros "#[HT | HT]"; [iApply "H1" | iApply "H2"]; iApply "HT".
  Qed.

  Lemma sDistr_And_Or_Stp Γ {S T U i} : ⊢ Γ s⊨ oAnd (oOr S T) U <:[i] oOr (oAnd S U) (oAnd T U).
  Proof.
    rewrite sstpd_eq'.
    by iIntros "!> %ρ %v #Hg !> [[HS|HT] Hu] /="; [iLeft|iRight]; iFrame.
  Qed.

  (* XXX must we state the two separate halves? *)
  Lemma sLater_Stp_Eq {Γ T U i} `{SwapPropI Σ}:
    Γ s⊨ T <:[i.+1] U ⊣⊢
    Γ s⊨ oLater T <:[i] oLater U.
  Proof. by rewrite sstpd_delay_oLaterN_plus. Qed.

  Lemma sStp_Add_LaterN {Γ T i j}:
    ⊢ Γ s⊨ T <:[i] oLaterN j T.
  Proof. rewrite sstpd_eq'; iIntros "!> ** !> $".  Qed.
  Lemma sStp_Add_Later {Γ T i}:
    ⊢ Γ s⊨ T <:[i] oLater T.
  Proof. apply sStp_Add_LaterN. Qed.

  Lemma sStp_Sel {Γ L U p l i}:
    Γ s⊨p p : cTMem l L U, i -∗
    Γ s⊨ L <:[i] oSel p l.
  Proof.
    rewrite sstpd_eq'; iIntros "#Hp !> %ρ %v Hg".
    iSpecialize ("Hp" with "Hg"); iNext i; iIntros "#HL".
    iApply (path_wp_wand with "Hp"); iIntros (w).
    iApply (vl_sel_lb with "HL").
  Qed.

  Lemma sSel_Stp {Γ L U p l i}:
    Γ s⊨p p : cTMem l L U, i -∗
    Γ s⊨ oSel p l <:[i] U.
  Proof.
    rewrite sstpd_eq'; iIntros "#Hp !> %ρ %v Hg".
    iSpecialize ("Hp" with "Hg"); iNext i; iIntros "Hφ".
    iDestruct (path_wp_agree with "Hp Hφ") as (w Hw) "[Hp Hφ]".
    iApply (vl_sel_ub with "Hφ Hp").
  Qed.

  Lemma sMu_Stp_Mu {Γ T1 T2 i} `{!SwapPropI Σ}:
    oLaterN i T1 :: Γ s⊨ T1 <:[i] T2 -∗
    Γ s⊨ oMu T1 <:[i] oMu T2.
  Proof.
    rewrite !sstpd_eq'; iIntros "/= #Hstp !> %ρ %v Hg".
    iApply mlaterN_impl; iIntros " #HT1".
    iApply ("Hstp" $! (v .: ρ) v with "[$Hg $HT1] [$HT1]").
  Qed.

  (** Novel subtyping rules. [Sub_Bind_1] and [Sub_Bind_2] become
  derivable. *)
  Lemma sMu_Stp {Γ T i} : ⊢ Γ s⊨ oMu (shift T) <:[i] T.
  Proof. rewrite oMu_shift. apply sStp_Refl. Qed.

  Lemma sStp_Mu {Γ T i} : ⊢ Γ s⊨ T <:[i] oMu (shift T).
  Proof. rewrite oMu_shift. apply sStp_Refl. Qed.

  Lemma sFld_Stp_Fld {Γ T1 T2 i l}:
    Γ s⊨ T1 <:[i] T2 -∗
    Γ s⊨ cVMem l T1 <:[i] cVMem l T2.
  Proof.
    iIntros "#Hsub !> %ρ Hg"; iSpecialize ("Hsub" with "Hg"); iNext i.
    iApply (cVMem_respects_sub with "Hsub").
  Qed.

  Lemma sTyp_Stp_Typ Γ L1 L2 U1 U2 i l :
    Γ s⊨ L2 <:[i] L1 -∗
    Γ s⊨ U1 <:[i] U2 -∗
    Γ s⊨ cTMem l L1 U1 <:[i] cTMem l L2 U2.
  Proof.
    iIntros "#HsubL #HsubU !> %ρ #Hg".
    iSpecialize ("HsubL" with "Hg"); iSpecialize ("HsubU" with "Hg"); iNext i.
    iApply (cTMem_respects_sub with "HsubL HsubU").
  Qed.

  Lemma sAll_Stp_All Γ T1 T2 U1 U2 i `{!SwapPropI Σ}:
    Γ s⊨ oLater T2 <:[i] oLater T1 -∗
    oLaterN (i.+1) (oShift T2) :: Γ s⊨ oLater U1 <:[i] oLater U2 -∗
    Γ s⊨ oAll T1 U1 <:[i] oAll T2 U2.
  Proof.
    rewrite !sstpd_delay_oLaterN_plus; iIntros "#HsubT #HsubU !> %ρ #Hg %v".
    rewrite -!mlaterN_impl.
    iDestruct 1 as (t) "#[Heq #HT1]"; iExists t; iFrame "Heq".
    iIntros (w); iSpecialize ("HT1" $! w).
    rewrite -!mlaterN_pers -!mlaterN_impl -!laterN_later.
    iIntros "!> #HwT2".
    iSpecialize ("HsubT" with "Hg").
    iSpecialize ("HsubU" $! (w .: ρ) with "[$HwT2 $Hg]").
    rewrite -!later_laterN !mlaterN_impl.
    iNext (i.+1); iModIntro. iApply (wp_wand with "(HT1 (HsubT HwT2))").
    iIntros (u) "#HuU1". iApply ("HsubU" with "HuU1").
  Qed.

  Lemma sSngl_Stp_Self Γ p T i :
    Γ s⊨p p : T, i -∗
    Γ s⊨ oSing p <:[i] T.
  Proof.
    rewrite sstpd_eq'; iIntros "#Hp !> %ρ %v Hg".
    iSpecialize ("Hp" with "Hg"); iNext i.
    iDestruct 1 as %->%(alias_paths_elim_eq (T _ ρ)).
    by rewrite path_wp_pv_eq.
  Qed.

  Lemma sSngl_Stp_Sym Γ p q T i:
    Γ s⊨p p : T, i -∗ (* Just to ensure [p] terminates and [oSing p] isn't empty. *)
    Γ s⊨ oSing p <:[i] oSing q -∗
    Γ s⊨ oSing q <:[i] oSing p.
  Proof.
    rewrite !sstpd_eq'; iIntros "#Hp #Hps !> %ρ %v #Hg".
    iDestruct (path_wp_eq with "(Hp Hg)") as (w) "[Hpw _] {Hp}".
    rewrite -alias_paths_pv_eq_1; iSpecialize ("Hps" $! _ w with "Hg Hpw");
      rewrite /= !alias_paths_pv_eq_1.
    iNext i; iRevert "Hps Hpw"; iIntros "!%" (Hqw Hpw Hqv).
    by rewrite /= (path_wp_pure_det Hqv Hqw).
  Qed.

  Lemma sSngl_pq_Stp {Γ i p q T1 T2} :
    T1 ~sTpI[ p := q ]* T2 -∗
    Γ s⊨p p : oSing q, i -∗
    Γ s⊨ T1 <:[i] T2.
  Proof.
    rewrite sstpd_eq'; iIntros "#Hrepl #Hal !> %ρ %v #Hg".
    iSpecialize ("Hal" with "Hg"); iNext i.
    iDestruct "Hal" as %Hal%alias_paths_simpl.
    iRewrite ("Hrepl" $! vnil ρ v Hal); iIntros "$".
  Qed.

  Lemma sD_Path_Stp {Γ T1 T2 p l}:
    Γ s⊨ T1 <:[0] T2 -∗
    Γ s⊨ { l := dpt p } : cVMem l T1 -∗
    Γ s⊨ { l := dpt p } : cVMem l T2.
  Proof.
    rewrite !sdtp_eq; iIntros "#Hsub #Hd !>" (ρ Hpid) "#Hg".
    iSpecialize ("Hd" $! ρ Hpid with "Hg"); rewrite !cVMem_eq.
    iApply (oDVMem_respects_sub with "(Hsub Hg) Hd").
  Qed.

  Lemma sD_Typ_Stp {Γ} L1 L2 U1 U2 s σ l:
    Γ s⊨ L2 <:[0] L1 -∗
    Γ s⊨ U1 <:[0] U2 -∗
    Γ s⊨ { l := dtysem σ s } : cTMem l L1 U1 -∗
    Γ s⊨ { l := dtysem σ s } : cTMem l L2 U2.
  Proof.
    rewrite !sdtp_eq; iIntros "#HL #HU #Hd !>" (ρ Hpid) "#Hg".
    iSpecialize ("Hd" $! ρ Hpid with "Hg"); rewrite !cTMem_eq.
    iApply (oDTMem_respects_sub with "(HL Hg) (HU Hg) Hd").
  Qed.

  Lemma sD_Typ_Abs_D {Γ} T L U s σ l:
    Γ s⊨ L <:[0] oLater T -∗
    Γ s⊨ oLater T <:[0] U -∗
    s ↝[ σ ] T -∗
    Γ s⊨ { l := dtysem σ s } : cTMem l L U.
  Proof. rewrite (sD_Typ l). apply sD_Typ_Stp. Qed.

  Lemma sP_DSub {Γ p T1 T2 i}:
    Γ s⊨p p : T1, i -∗
    Γ s⊨ T1 <:[i] T2 -∗
    (*───────────────────────────────*)
    Γ s⊨p p : T2, i.
  Proof.
    iIntros "#HpT1 #Hsub !> %ρ #Hg".
    iSpecialize ("Hsub" with "Hg"); iSpecialize ("HpT1" with "Hg"); iNext i.
    iApply (path_wp_wand with "HpT1"); iIntros "%w HvT1 {Hg HpT1}".
    iApply ("Hsub" with "HvT1").
  Qed.

  Lemma sP_Later {Γ} p T i :
    Γ s⊨p p : oLater T, i -∗
    Γ s⊨p p : T, S i.
  Proof.
    iIntros "#HpT !> %ρ #Hg"; rewrite laterN_later.
    iSpecialize ("HpT" with "Hg"); iNext i.
    iApply (path_wp_later_swap with "HpT").
  Qed.

  Lemma sT_Skip Γ e T :
    Γ s⊨ e : oLater T -∗
    Γ s⊨ tskip e : T.
  Proof.
    iIntros "#HT !> * #Hg !>"; iSpecialize ("HT" with "Hg").
    smart_wp_bind SkipCtx v "#Hr" "HT".
    by rewrite -wp_pure_step_later // -wp_value.
  Qed.

  Lemma sT_DSub {Γ e T1 T2}:
    Γ s⊨ e : T1 -∗
    Γ s⊨ T1 <:[0] T2 -∗
    (*───────────────────────────────*)
    Γ s⊨ e : T2.
  Proof.
    iIntros "#HeT1 #Hsub !> %ρ #Hg !>".
    iApply (wp_wand with "(HeT1 Hg)").
    iIntros (v) "#HvT1 {HeT1} /=".
    iApply ("Hsub" with "Hg HvT1").
  Qed.
End DStpLemmas.

Section SynLemmas.
  Context `{HdotG: !dlangG Σ}.

  Lemma All_Stp_All {Γ} T1 T2 U1 U2 i `{!SwapPropI Σ}:
    Γ ⊨ TLater T2 <:[i] TLater T1 -∗
    iterate TLater i.+1 (shift T2) :: Γ ⊨ TLater U1 <:[i] TLater U2 -∗
    Γ ⊨ TAll T1 U1 <:[i] TAll T2 U2.
  Proof.
    rewrite /istpd fmap_cons iterate_TLater_oLater.
    rewrite (interp_subst_commute T2 (ren (+1))).
    apply: sAll_Stp_All.
  Qed.

  Lemma Sngl_pq_Stp {Γ i p q T1 T2} (Hrepl : T1 ~Tp[ p := q ]* T2):
    Γ ⊨p p : TSing q, i -∗
    Γ ⊨ T1 <:[i] T2.
  Proof.
    iApply sSngl_pq_Stp; iApply sem_ty_path_repl_eq.
    apply fundamental_ty_path_repl_rtc, Hrepl.
  Qed.
End SynLemmas.

Section iSub_Derived_Lemmas.
  Context `{HdotG: !dlangG Σ}.

  Lemma sstpd0_to_sstpi0 Γ T1 T2 :
    Γ s⊨ T1 <:[0] T2 ⊣⊢
    Γ s⊨ T1, 0 <: T2, 0.
  Proof. by rewrite /sstpi sstpd_eq'. Qed.

  Lemma sstpi_to_sstpd0 Γ i j T1 T2 :
    Γ s⊨ T1, i <: T2, j ⊣⊢
    Γ s⊨ oLaterN i T1 <:[0] oLaterN j T2.
  Proof. by rewrite sstpd0_to_sstpi0. Qed.

  (* Show the following statements are derivable. *)
  Lemma sSub_And' Γ T U1 U2 i j:
    Γ s⊨ T, i <: U1, j -∗
    Γ s⊨ T, i <: U2, j -∗
    Γ s⊨ T, i <: oAnd U1 U2, j.
  Proof. rewrite !sstpi_to_sstpd0 sTEq_oAnd_oLaterN. apply sStp_And. Qed.

  Lemma sOr_Sub Γ T1 T2 U i j:
    Γ s⊨ T1, i <: U, j -∗
    Γ s⊨ T2, i <: U, j -∗
    Γ s⊨ oOr T1 T2, i <: U, j.
  Proof. rewrite !sstpi_to_sstpd0 sTEq_oOr_oLaterN. apply sOr_Stp. Qed.
End iSub_Derived_Lemmas.

Section iSub_Derived_Lemmas.
  Context `{HdotG: !dlangG Σ} `{!SwapPropI Σ}.

  Lemma sstpd_to_sstpi Γ i T1 T2 :
    Γ s⊨ T1 <:[i] T2 ⊣⊢
    Γ s⊨ T1, i <: T2, i.
  Proof. by rewrite /sstpi -sstpd_delay_oLaterN sstpd_eq'. Qed.

  Lemma sMu_Sub_Mu {Γ T1 T2 i j} :
    oLaterN i T1 :: Γ s⊨ T1, i <: T2, j -∗
    Γ s⊨ oMu T1, i <: oMu T2, j.
  Proof.
    rewrite !sstpi_to_sstpd0 !sTEq_oMu_oLaterN.
    rewrite -sMu_Stp_Mu.
    by rewrite -oLaterN_plus.
  Qed.
End iSub_Derived_Lemmas.
