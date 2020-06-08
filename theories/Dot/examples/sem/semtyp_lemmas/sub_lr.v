(** * Semantic lemmas for double-delay subtyping. *)
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

From D Require Import iris_prelude succ_notation swap_later_impl proper.
From D.Dot Require Import rules path_repl unary_lr dsub_lr defs_lr.

Implicit Types (Σ : gFunctors)
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : env) (l : label).

Section defs.
  Context {Σ}.
  Implicit Types (τ : oltyO Σ 0).

  (** Legacy: (double)-indexed subtyping. *)
  Definition sstpi `{!dlangG Σ} i j Γ τ1 τ2 : iProp Σ :=
    □∀ ρ v,
      sG⟦Γ⟧*ρ → ▷^i oClose τ1 ρ v → ▷^j oClose τ2 ρ v.
  Global Arguments sstpi /.

  Context `{!dlangG Σ}.
  Definition istpi Γ T1 T2 i j := sstpi i j V⟦Γ⟧* V⟦T1⟧ V⟦T2⟧.
  (* Avoid auto-dropping box (and unfolding) when introducing judgments persistently. *)
  Local Notation IntoPersistent' P := (IntoPersistent false P P).
  Global Instance sstpi_persistent i j Γ T1 T2 : IntoPersistent' (sstpi i j Γ T1 T2) | 0 := _.
  Global Instance istpi_persistent Γ T1 T2 i j : IntoPersistent' (istpi Γ T1 T2 i j) | 0 := _.
End defs.
(** Indexed subtyping *)
Notation "Γ s⊨ T1 , i <: T2 , j " := (sstpi i j Γ T1 T2) (at level 74, T1, T2, i, j at next level).
Notation "Γ ⊨ T1 , i <: T2 , j" := (istpi Γ T1 T2 i j) (at level 74, T1, T2, i, j at next level).

(** * Proper instances. *)
Section Propers.
  Context `{HdotG: !dlangG Σ}.
  Implicit Types (τ L T U : olty Σ 0).

  Global Instance sstpi_proper i j : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (sstpi i j).
  Proof.
    solve_proper_ho.
    (* intros ?? HG ?? H1 ?? H2; simplify_eq/=.
    properness; [by rewrite HG|apply H1|apply H2]. *)
  Qed.
  Global Instance sstpi_flip_proper i j :
    Proper ((≡) --> (≡) --> (≡) --> flip (≡)) (sstpi i j).
  Proof. apply: flip_proper_4. Qed.
  Global Instance: Params (@sstpi) 4 := {}.
End Propers.

Section judgment_lemmas.
  Context `{!dlangG Σ}.

  (** ** Show this typing judgment is equivalent to the more direct definition. *)
  Lemma istpi_eq Γ T1 i T2 j :
    Γ ⊨ T1, i <: T2, j ⊣⊢
    □∀ ρ v, G⟦Γ⟧ ρ → ▷^i V⟦T1⟧ vnil ρ v → ▷^j V⟦T2⟧ vnil ρ v.
  Proof. reflexivity. Qed.

  Lemma sstpi_app ρ Γ T1 T2 i j :
    Γ s⊨ T1, i <: T2, j -∗ sG⟦ Γ ⟧* ρ -∗
    oClose (oLaterN i T1) ρ ⊆ oClose (oLaterN j T2) ρ.
  Proof. iIntros "Hsub Hg %v"; iApply ("Hsub" with "Hg"). Qed.

  Lemma sstpd0_to_sstpi0 Γ T1 T2 :
    Γ s⊨ T1 <:[0] T2 ⊣⊢
    Γ s⊨ T1, 0 <: T2, 0.
  Proof. by rewrite /sstpi sstpd_eq. Qed.

  Lemma sstpi_to_sstpd0 Γ i j T1 T2 :
    Γ s⊨ T1, i <: T2, j ⊣⊢
    Γ s⊨ oLaterN i T1 <:[0] oLaterN j T2.
  Proof. by rewrite sstpd0_to_sstpi0. Qed.

  Lemma sstpd_to_sstpi Γ i T1 T2  `{!SwapPropI Σ} :
    Γ s⊨ T1 <:[i] T2 ⊣⊢
    Γ s⊨ T1, i <: T2, i.
  Proof. by rewrite /sstpi -sstpd_delay_oLaterN sstpd_eq. Qed.
End judgment_lemmas.

Section StpLemmas.
  Context `{HdotG: !dlangG Σ}.

  Lemma sSub_Refl {Γ} T i : ⊢ Γ s⊨ T, i <: T, i.
  Proof. by iIntros "!> **". Qed.

  Lemma sSub_Trans {Γ T1 T2 T3 i1 i2 i3} : Γ s⊨ T1, i1 <: T2, i2 -∗
                                      Γ s⊨ T2, i2 <: T3, i3 -∗
                                      Γ s⊨ T1, i1 <: T3, i3.
  Proof.
    iIntros "#Hsub1 #Hsub2 !> * #Hg HT".
    iApply ("Hsub2" with "Hg (Hsub1 Hg HT)").
  Qed.

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
  Proof. rewrite !sstpi_to_sstpd0 sTEq_oAnd_oLaterN. apply sStp_And. Qed.

  Lemma sSub_Or1 Γ T1 T2 i: ⊢ Γ s⊨ T1, i <: oOr T1 T2, i.
  Proof. by iIntros "!> * _ ? !> /="; eauto. Qed.
  Lemma sSub_Or2 Γ T1 T2 i: ⊢ Γ s⊨ T2, i <: oOr T1 T2, i.
  Proof. by iIntros "!> * _ ? !> /="; eauto. Qed.

  Lemma sOr_Sub Γ T1 T2 U i j:
    Γ s⊨ T1, i <: U, j -∗
    Γ s⊨ T2, i <: U, j -∗
    Γ s⊨ oOr T1 T2, i <: U, j.
  Proof. rewrite !sstpi_to_sstpd0 sTEq_oOr_oLaterN. apply sOr_Stp. Qed.

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
    Γ s⊨ L, i <: oSel p l, i.
  Proof.
    iIntros "/= #Hp !> %ρ %v Hg #HL"; iSpecialize ("Hp" with "Hg"); iNext i.
    iApply (path_wp_wand with "Hp"); iIntros (w).
    iApply (vl_sel_lb with "HL").
  Qed.

  Lemma sSel_Sub {Γ L U p l i}:
    Γ s⊨p p : cTMem l L U, i -∗
    Γ s⊨ oSel p l, i <: U, i.
  Proof.
    iIntros "#Hp !> %ρ %v Hg Hφ"; iSpecialize ("Hp" with "Hg"); iNext i.
    iDestruct (path_wp_agree with "Hp Hφ") as (w Hw) "[Hp Hφ]".
    iApply (vl_sel_ub with "Hφ Hp").
  Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂ᶻ
     ----------------------------------------------- (μ-<:-μ)
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


  Lemma sFld_Sub_Fld {Γ T1 T2 i l}:
    Γ s⊨ T1, i <: T2, i -∗
    Γ s⊨ cVMem l T1, i <: cVMem l T2, i.
  Proof.
    iIntros "#Hsub !> %ρ %v Hg HT1"; iApply (cVMem_respects_subN with "[Hg] HT1").
    iApply (sstpi_app with "Hsub Hg").
  Qed.

  Lemma sAll_Sub_All {Γ T1 T2 U1 U2 i} `{!SwapPropI Σ} :
    Γ s⊨ oLater T2, i <: oLater T1, i -∗
    oLaterN (S i) (shift T2) :: Γ s⊨ oLater U1, i <: oLater U2, i -∗
    Γ s⊨ oAll T1 U1, i <: oAll T2 U2, i.
  Proof. rewrite -!sstpd_to_sstpi. apply: sAll_Stp_All. Qed.

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
    Γ s⊨ L2, i <: L1, i -∗
    Γ s⊨ U1, i <: U2, i -∗
    Γ s⊨ cTMem l L1 U1, i <: cTMem l L2 U2, i.
  Proof. rewrite -!sstpd_to_sstpi. apply sTyp_Stp_Typ. Qed.

  Lemma sD_Path_Sub {Γ T1 T2 p l}:
    Γ s⊨ T1, 0 <: T2, 0 -∗
    Γ s⊨ { l := dpt p } : cVMem l T1 -∗
    Γ s⊨ { l := dpt p } : cVMem l T2.
  Proof.
    rewrite !sdtp_eq'; iIntros "#Hsub #Hv !>" (ρ Hpid) "#Hg".
    iSpecialize ("Hv" $! ρ Hpid with "Hg"); rewrite !oDVMem_eq.
    iApply (path_wp_wand with "Hv"); iIntros "{Hv} %v #Hv".
    iApply ("Hsub" with "Hg Hv").
  Qed.

  (** ** Type member introduction. *)
  Lemma sD_Typ_Sub {Γ} L1 L2 U1 U2 s σ l:
    Γ s⊨ L2, 0 <: L1, 0 -∗
    Γ s⊨ U1, 0 <: U2, 0 -∗
    Γ s⊨ { l := dtysem σ s } : cTMem l L1 U1 -∗
    Γ s⊨ { l := dtysem σ s } : cTMem l L2 U2.
  Proof.
    rewrite !sdtp_eq'; iIntros "#HL #HU #Hd !>" (ρ Hpid) "#Hg".
    iSpecialize ("Hd" $! ρ Hpid with "Hg").
    iDestruct "Hd" as (ψ) "(Hφ & HLψ & HψU)".
    iExists ψ. iFrame "Hφ"; iClear "Hφ".
    iModIntro; repeat iSplit; iIntros (v) "#H".
    - iApply ("HLψ" with "(HL Hg H)").
    - iApply ("HU" with "Hg (HψU H)").
  Qed.

  Lemma sD_Typ_Abs {Γ} T L U s σ l:
    Γ s⊨ L, 0 <: oLater T, 0 -∗
    Γ s⊨ oLater T, 0 <: U, 0 -∗
    s ↝[ σ ] T -∗
    Γ s⊨ { l := dtysem σ s } : cTMem l L U.
  Proof. rewrite (sD_Typ l). apply sD_Typ_Sub. Qed.

  Lemma sSngl_Sub_Self Γ p T i :
    Γ s⊨p p : T, i -∗
    Γ s⊨ oSing p, i <: T, i.
  Proof.
    iIntros "#Hp !> %ρ %v Hg /= Heq"; iSpecialize ("Hp" with "Hg"); iNext i.
    iDestruct "Heq" as %->%(alias_paths_elim_eq (T _ ρ)).
    by rewrite path_wp_pv_eq.
  Qed.

  Lemma sSngl_Sub_Sym Γ p q T i:
    Γ s⊨p p : T, i -∗ (* Just to ensure [p] terminates and [oSing p] isn't empty. *)
    Γ s⊨ oSing p, i <: oSing q, i -∗
    Γ s⊨ oSing q, i <: oSing p, i.
  Proof.
    iIntros "#Hp #Hps !> %ρ %v #Hg Heq".
    iDestruct (path_wp_eq with "(Hp Hg)") as (w) "[Hpw _] {Hp}".
    rewrite -alias_paths_pv_eq_1; iSpecialize ("Hps" $! _ w with "Hg Hpw");
      iNext i; rewrite /= !alias_paths_pv_eq_1.
    iRevert "Hps Hpw Heq"; iIntros "!%" (Hqw Hpw Hqv).
    rewrite (path_wp_pure_det Hqv Hqw) {Hqv Hqw}. exact Hpw.
  Qed.

  (** Here we show this rule for *semantic* substitution. *)
  Lemma sSngl_pq_Sub {Γ i p q T1 T2} :
    T1 ~sTpI[ p := q ]* T2 -∗
    Γ s⊨p p : oSing q, i -∗
    Γ s⊨ T1, i <: T2, i.
  Proof.
    iIntros "#Hrepl #Hal !> %ρ %v Hg HT1".
    iSpecialize ("Hal" with "Hg"); iNext i.
    iDestruct "Hal" as %Hal%alias_paths_simpl.
    iRewrite -("Hrepl" $! vnil ρ v Hal); iExact "HT1".
  Qed.

  Lemma Sngl_pq_Sub {Γ i p q T1 T2} (Hrepl : T1 ~Tp[ p := q ]* T2):
    Γ ⊨p p : TSing q, i -∗
    Γ ⊨ T1, i <: T2, i.
  Proof.
    iApply sSngl_pq_Sub; iApply sem_ty_path_repl_eq.
    apply fundamental_ty_path_repl_rtc, Hrepl.
  Qed.

  Lemma sP_ISub {Γ p T1 T2 i j}:
    Γ s⊨p p : T1, i -∗
    Γ s⊨ T1, i <: T2, i + j -∗
    (*───────────────────────────────*)
    Γ s⊨p p : T2, i + j.
  Proof.
    iIntros "/= * #HpT1 #Hsub !> * #Hg".
    iSpecialize ("HpT1" with "Hg").
    rewrite !path_wp_eq.
    iDestruct "HpT1" as (v) "Hpv"; iExists v.
    iDestruct "Hpv" as "[$ HpT1] {Hpv}". by iApply "Hsub".
  Qed.

  Lemma sT_ISub {Γ e T1 T2 i}:
    Γ s⊨ e : T1 -∗
    Γ s⊨ T1, 0 <: T2, i -∗
    (*───────────────────────────────*)
    Γ s⊨ iterate tskip i e : T2.
  Proof.
    iIntros "/= #HeT1 #Hsub !> %ρ #Hg !>".
    rewrite tskip_subst -wp_bind.
    iApply (wp_wand with "(HeT1 Hg)").
    iIntros (v) "#HvT1".
    (* We can swap ▷^i with WP (tv v)! *)
    rewrite -wp_pure_step_later // -wp_value.
    by iApply "Hsub".
  Qed.

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

(* In this section, some lemmas about double-delay subtyping are derived from
the above ones. *)
Section iSub_Derived_Lemmas.
  Context `{HdotG: !dlangG Σ} `{!SwapPropI Σ}.

  Lemma sSub_Skolem_P {Γ T1 T2 i j}:
    oLaterN i (shift T1) :: Γ s⊨p pv (ids 0) : shift T2, j -∗
    (*───────────────────────────────*)
    Γ s⊨ T1, i <: T2, j.
  Proof. by rewrite !sstpi_to_sstpd0 -sStp_Skolem_P oLaterN_0. Qed.

  Lemma Sub_Skolem_P {Γ T1 T2 i j}:
    iterate TLater i (shift T1) :: Γ ⊨p pv (ids 0) : shift T2, j -∗
    (*───────────────────────────────*)
    Γ ⊨ T1, i <: T2, j.
  Proof.
    rewrite /iptp fmap_cons iterate_TLater_oLater !interp_subst_commute.
    exact: sSub_Skolem_P.
  Qed.
End iSub_Derived_Lemmas.
