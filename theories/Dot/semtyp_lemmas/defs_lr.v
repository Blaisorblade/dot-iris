(** * Semantic lemmas for definition typing. *)
From iris.proofmode Require Import proofmode.
From D.Dot Require Import dot_semtypes.

Implicit Types (v : vl) (e : tm) (d : dm) (ds : dms).

Section Sec.
  Context `{HdotG : !dlangG Σ} `{!RecTyInterp Σ}.

  (** Lemmas about definition typing. *)
  Lemma sD_Path {Γ} T p l :
    Γ s⊨p p : T, 0 -∗
    Γ s⊨ { l := dpt p } : cVMem l T.
  Proof.
    rewrite sdtp_eq'; pupd; iIntros "#Hv !>" (ρ Hpid) "#Hg".
    rewrite oDVMem_eq; iApply ("Hv" with "Hg").
  Qed.

  (**
  Beware this lemma does not extend to unstamped semantic typing.
  As such, it should only be used in lemmas like [sD_Val]. *)
  Lemma sP_Val {Γ} v T :
    Γ s⊨ tv v : T -∗
    Γ s⊨p pv v : T, 0.
  Proof.
    pupd; iIntros "/= #Hp !> %ρ Hg". rewrite path_wp_pv_eq -wp_value_inv'.
    iApply ("Hp" with "Hg").
  Qed.

  Lemma sD_Val {Γ} T v l :
    Γ s⊨ tv v : T -∗
    Γ s⊨ { l := dpt (pv v) } : cVMem l T.
  Proof. by rewrite -sD_Path -sP_Val. Qed.

  (** This lemma is equivalent to pDOT's (Def-New). *)
  Lemma sD_Val_New {Γ l ds} {T : clty Σ} :
    oAnd (oLater T) (oSing (pself (pv (ids 1)) l)) :: Γ s⊨ds ds : T -∗
    Γ s⊨ { l := dpt (pv (vobj ds)) } : cVMem l (oMu T).
  Proof.
    rewrite sdtp_eq'. pupd.
    iIntros "[%Hwf #Hds] !>" (ρ Hpid%path_includes_field_aliases) "#Hg".
    rewrite oDVMem_eq path_wp_pv_eq /=. iLöb as "IH".
    iEval rewrite -clty_commute norm_selfSubst.
    iApply ("Hds" $! (vobj _ .: ρ) with "[%] [$IH $Hg //]").
    exact: path_includes_self.
  Qed.

  Lemma sD_Path_Stp {Γ T1 T2 p l} :
    Γ s⊨ T1 <:[0] T2 -∗
    Γ s⊨ { l := dpt p } : cVMem l T1 -∗
    Γ s⊨ { l := dpt p } : cVMem l T2.
  Proof.
    rewrite !sdtp_eq'; pupd; iIntros "#Hsub #Hd !>" (ρ Hpid) "#Hg".
    iSpecialize ("Hd" $! ρ Hpid with "Hg").
    iApply (oDVMem_respects_sub with "(Hsub Hg) Hd").
  Qed.

  Lemma sD_Typ_Stp {Γ} L1 L2 U1 U2 d l :
    Γ s⊨ L2 <:[0] L1 -∗
    Γ s⊨ U1 <:[0] U2 -∗
    Γ s⊨ { l := d } : cTMem l L1 U1 -∗
    Γ s⊨ { l := d } : cTMem l L2 U2.
  Proof.
    rewrite !sdtp_eq'; pupd; iIntros "#HL #HU #Hd !>" (ρ Hpid) "#Hg".
    iSpecialize ("Hd" $! ρ Hpid with "Hg").
    iApply (oDTMem_respects_sub with "(HL Hg) (HU Hg) Hd").
  Qed.

  Lemma sD_Typ {Γ s σ} {T : oltyO Σ} l :
    s ↝[ σ ] T -∗
    Γ s⊨ { l := dtysem σ s } : cTMem l (oLater T) (oLater T).
  Proof.
    rewrite !sdtp_eq'; pupd; iDestruct 1 as (φ Hγφ) "#Hγ".
    iIntros "!>" (ρ Hpid) "#Hg"; rewrite oDTMem_unfold /=.
    iExists (hoEnvD_inst (σ.|[ρ]) φ); iSplit.
    by iApply (dm_to_type_intro with "Hγ").
    iSplit; iIntros "%v #H"; iNext; by iApply Hγφ.
  Qed.

  Lemma sD_Typ_Abs {Γ} T L U s σ l :
    Γ s⊨ L <:[0] oLater T -∗
    Γ s⊨ oLater T <:[0] U -∗
    s ↝[ σ ] T -∗
    Γ s⊨ { l := dtysem σ s } : cTMem l L U.
  Proof. rewrite (sD_Typ l). apply sD_Typ_Stp. Qed.

  (** ** Prove object introduction for path typing, using Löb induction:

    Γ, x : ▷ T ⊨ ds : T
    ---------------------
    Γ ⊨p nu x. ds : μ x. T, 0
  *)
  Lemma sP_Obj_I (Γ : sCtx Σ) (T : clty Σ) ds :
    oLater T :: Γ s⊨ds ds : T -∗
    Γ s⊨p pv (vobj ds) : oMu T, 0.
  Proof.
    pupd; iIntros "[%Hwf #Hds] !> %ρ #Hg /=".
    rewrite path_wp_pv_eq /=. iLöb as "IH".
    iApply clty_commute. rewrite norm_selfSubst.
    iApply ("Hds" $! (vobj _ .: ρ) with "[%] [$IH $Hg]").
    exact: path_includes_self.
  Qed.

  (** ** Derive object introduction for term typing. *)
  Lemma sT_Obj_I (Γ : sCtx Σ) (T : clty Σ) ds :
    oLater T :: Γ s⊨ds ds : T -∗ Γ s⊨ tv (vobj ds) : oMu T.
  Proof. by rewrite sP_Obj_I sT_Path. Qed.

  Lemma sD_Nil Γ : ⊢ Γ s⊨ds [] : cTop.
  Proof. by pupd; iIntros "!>"; iSplit; last iIntros "**". Qed.

  Lemma sD_Cons Γ d ds l (T1 T2 : cltyO Σ) :
    dms_hasnt ds l →
    Γ s⊨ { l := d } : T1 -∗ Γ s⊨ds ds : T2 -∗
    Γ s⊨ds (l, d) :: ds : cAnd T1 T2.
  Proof.
    rewrite sdtp_eq => Hlds; pupd; iIntros "#HT1 [% #HT2] !>"; iSplit.
    by iIntros "!%"; cbn; constructor => //; by rewrite -dms_hasnt_notin_eq.
    iIntros (ρ [Hpid Hpids]%path_includes_split) "#Hg".
    iSpecialize ("HT1" $! _ Hpid with "Hg").
    iSpecialize ("HT2" $! _ Hpids with "Hg").
    iSplit; first by iApply clty_def2defs_head.
    iApply (clty_mono with "HT2"). exact: dms_hasnt_subst.
  Qed.

  (* Useful derived rules. *)
  Lemma sD_Sing Γ d l T : Γ s⊨ { l := d } : T -∗ Γ s⊨ds [(l, d)] : cAnd T cTop.
  Proof. by iIntros "#H"; iApply (sD_Cons with "H"); last iApply sD_Nil. Qed.

  (** Not part of the official type system, but very convenient for examples. *)
  Lemma sD_Sing' Γ d l T : Γ s⊨ { l := d } : T -∗ Γ s⊨ds [(l, d)] : T.
  Proof. by rewrite sD_Sing (cAnd_cTop T). Qed.
End Sec.
