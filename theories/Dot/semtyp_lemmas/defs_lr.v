(** * Semantic lemmas for definition typing. *)
From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr.

Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms).

Set Suggest Proof Using.
Set Default Proof Using "Type".

Section Sec.
  Context `{HdlangG: !dlangG Σ}.

  (** Lemmas about definition typing. *)
  Lemma sD_Path {Γ} T p l:
    Γ s⊨p p : T, 0 -∗
    Γ s⊨ { l := dpt p } : cVMem l T.
  Proof.
    rewrite sdtp_eq; iIntros "#Hv !>" (ρ Hpid) "#Hg".
    rewrite cVMem_dpt_eq; iApply ("Hv" with "Hg").
  Qed.


  Lemma D_Path {Γ} T p l:
    Γ ⊨p p : T, 0 -∗ Γ ⊨ { l := dpt p } : TVMem l T.
  Proof. apply sD_Path. Qed.

  Lemma sD_Val {Γ} T v l:
    Γ s⊨ tv v : T -∗
    Γ s⊨ { l := dpt (pv v) } : cVMem l T.
  Proof. by rewrite -sD_Path -sP_Val. Qed.

  Lemma D_Val {Γ} T v l:
    Γ ⊨ tv v : T -∗ Γ ⊨ { l := dpt (pv v) } : TVMem l T.
  Proof. apply sD_Val. Qed.

  (** This lemma is equivalent to pDOT's (Def-New). *)
  Lemma sD_Val_New {Γ l ds} {T : clty Σ}:
    oAnd (oLater T) (oSing (pself (pv (ids 1)) l)) :: Γ s⊨ds ds : T -∗
    Γ s⊨ { l := dpt (pv (vobj ds)) } : cVMem l (oMu (clty_olty T)).
  Proof.
    rewrite sdtp_eq; iDestruct 1 as (Hwf) "#Hds";
      iIntros "!>" (ρ Hpid%path_includes_field_aliases) "#Hg".
    rewrite cVMem_dpt_eq path_wp_pv_eq /=. iLöb as "IH".
    iApply clty_commute. rewrite norm_selfSubst.
    iApply ("Hds" $! (vobj _ .: ρ) with "[%] [$IH $Hg //]").
    exact: path_includes_self.
  Qed.

  Lemma D_Val_New Γ T l ds:
    TAnd (TLater T) (TSing (pself (pv (ids 1)) l)) :: Γ ⊨ds ds : T -∗
    Γ ⊨ { l := dpt (pv (vobj ds)) } : TVMem l (TMu T).
  Proof. apply sD_Val_New. Qed.

  Lemma sD_Path_Sub {Γ T1 T2 p l}:
    Γ s⊨ T1, 0 <: T2, 0 -∗
    Γ s⊨ { l := dpt p } : cVMem l T1 -∗
    Γ s⊨ { l := dpt p } : cVMem l T2.
  Proof.
    rewrite !sdtp_eq; iIntros "#Hsub #Hv !>" (ρ Hpid) "#Hg".
    iSpecialize ("Hv" $! ρ Hpid with "Hg"); rewrite !cVMem_dpt_eq.
    iApply (path_wp_wand with "Hv"); iIntros "!> **".
    by iApply ("Hsub" with "Hg").
  Qed.

  Lemma D_Path_Sub {Γ T1 T2 p l}:
    Γ ⊨ T1, 0 <: T2, 0 -∗
    Γ ⊨ { l := dpt p } : TVMem l T1 -∗
    Γ ⊨ { l := dpt p } : TVMem l T2.
  Proof. apply sD_Path_Sub. Qed.

  (** ** Type member introduction. *)
  Lemma sD_Typ_Abs {Γ} T L U s σ l:
    Γ s⊨ oLater T, 0 <: oLater U, 0 -∗
    Γ s⊨ oLater L, 0 <: oLater T, 0 -∗
    s ↝[ σ ] T -∗
    Γ s⊨ { l := dtysem σ s } : cTMem l L U.
  Proof.
    rewrite !sdtp_eq; iIntros "#HTU #HLT #Hs !>" (ρ Hpid) "#Hg".
    rewrite cTMem_eq; iDestruct "Hs" as (φ Hγφ) "Hγ".
    iExists (hoEnvD_inst (σ.|[ρ]) φ); iSplit.
    by iApply (dm_to_type_intro with "Hγ").
    iModIntro; repeat iSplit; iIntros (v) "#HL";
      rewrite /= later_intuitionistically.
    - iIntros "!>". iApply Hγφ. by iApply "HLT".
    - iApply ("HTU" with "Hg"). by iApply Hγφ.
  Qed.

  Lemma D_Typ_Abs {Γ} T L U s σ l:
    Γ ⊨ TLater T, 0 <: TLater U, 0 -∗
    Γ ⊨ TLater L, 0 <: TLater T, 0 -∗
    s ↝[ σ ] V⟦ T ⟧ -∗
    Γ ⊨ { l := dtysem σ s } : TTMem l L U.
  Proof. apply sD_Typ_Abs. Qed.

  Lemma sD_Typ {Γ} (T : oltyO Σ 0) s σ l:
    s ↝[ σ ] T -∗
    Γ s⊨ { l := dtysem σ s } : cTMem l T T.
  Proof. by iIntros "#Hs"; iApply sD_Typ_Abs; [> iApply sSub_Refl ..|]. Qed.

  Lemma D_Typ {Γ} T s σ l:
    s ↝[ σ ] V⟦ T ⟧ -∗
    Γ ⊨ { l := dtysem σ s } : TTMem l T T.
  Proof. apply sD_Typ. Qed.

  (** ** Prove object introduction rule, using Löb induction:
   *
   * Γ, x: ▷ T ⊨ ds : T
   * ---------------------
   * Γ ⊨ nu x. ds : μ x. T
   *)
  Lemma sT_Obj_I (Γ : sCtx Σ) (T : clty Σ) ds:
     oLater T :: Γ s⊨ds ds : T -∗
     Γ s⊨ tv (vobj ds) : oMu T.
  Proof.
    iDestruct 1 as (Hwf) "#Hds"; iIntros "!> %ρ #Hg /= !>".
    rewrite -wp_value' /=. iLöb as "IH".
    iApply clty_commute. rewrite norm_selfSubst.
    iApply ("Hds" $! (vobj _ .: ρ) with "[%] [$IH $Hg]").
    exact: path_includes_self.
  Qed.

  Lemma T_Obj_I Γ T ds:
     Γ |L T ⊨ds ds : T -∗
     Γ ⊨ tv (vobj ds) : TMu T.
  Proof. apply sT_Obj_I. Qed.

  Lemma sD_Nil Γ : ⊢ Γ s⊨ds [] : cTop.
  Proof. by iSplit; last iIntros "!> **". Qed.

  Lemma D_Nil Γ : ⊢ Γ ⊨ds [] : TTop.
  Proof. apply sD_Nil. Qed.

  Lemma sD_Cons Γ d ds l (T1 T2 : cltyO Σ):
    dms_hasnt ds l →
    Γ s⊨ { l := d } : T1 -∗ Γ s⊨ds ds : T2 -∗
    Γ s⊨ds (l, d) :: ds : cAnd T1 T2.
  Proof.
    rewrite !sdtp_eq; iIntros (Hlds) "#HT1 [% #HT2]"; iSplit.
    by iIntros "!%"; cbn; constructor => //; by rewrite -dms_hasnt_notin_eq.
    iIntros "!>" (ρ [Hpid Hpids]%path_includes_split) "#Hg".
    iSpecialize ("HT1" $! _  Hpid with "Hg").
    iDestruct ("HT2" $! _  Hpids with "Hg") as "{HT2} HT2".
    iSplit; first by iApply clty_def2defs_head.
    iApply (clty_mono with "HT2"); by [apply dms_hasnt_subst | eapply nclosed_sub_app].
  Qed.

  Lemma D_Cons Γ d ds l T1 T2:
    dms_hasnt ds l →
    Γ ⊨ { l := d } : T1 -∗ Γ ⊨ds ds : T2 -∗
    Γ ⊨ds (l, d) :: ds : TAnd T1 T2.
  Proof. apply sD_Cons. Qed.
End Sec.
