From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr.

Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms).

Section Sec.
  Context `{HdlangG: dlangG Σ}.

  Lemma sP_Val {Γ} v T:
    Γ s⊨ tv v : T -∗
    Γ s⊨p pv v : T, 0.
  Proof.
    iIntros "/= #Hp !>" (ρ) "Hg"; iSpecialize ("Hp" with "Hg").
    by rewrite /= wp_value_inv' path_wp_pv.
  Qed.

  Lemma P_Val {Γ} v T: Γ ⊨ tv v : T -∗ Γ ⊨p pv v : T, 0.
  Proof. apply sP_Val. Qed.

  (** Lemmas about definition typing. *)
  Lemma sD_Path_TVMem_I {Γ} T p l:
    Γ s⊨p p : T, 0 -∗
    Γ s⊨ { l := dpt p } : cVMem l T.
  Proof.
    iIntros "#Hv !>" (ρ Hpid) "#Hg".
    rewrite def_interp_tvmem_eq.
    iApply ("Hv" with "Hg").
  Qed.

  Lemma D_Path_TVMem_I {Γ} T p l:
    Γ ⊨p p : T, 0 -∗ Γ ⊨ { l := dpt p } : TVMem l T.
  Proof. apply sD_Path_TVMem_I. Qed.

  Lemma sD_TVMem_I {Γ} T v l:
    Γ s⊨ tv v : T -∗
    Γ s⊨ { l := dpt (pv v) } : cVMem l T.
  Proof. by rewrite -sD_Path_TVMem_I -sP_Val. Qed.

  Lemma D_TVMem_I {Γ} T v l:
    Γ ⊨ tv v : T -∗ Γ ⊨ { l := dpt (pv v) } : TVMem l T.
  Proof. apply sD_TVMem_I. Qed.

  (** This lemma is equivalent to pDOT's (Def-New). *)
  Lemma sD_New_Mem_I {Γ l ds} {T : clty Σ}:
    oAnd (oLater T) (oSing (pself (pv (ids 1)) l)) :: Γ s⊨ds ds : T -∗
    Γ s⊨ { l := dpt (pv (vobj ds)) } : cVMem l (oMu (clty_olty T)).
  Proof.
    iDestruct 1 as (Hwf) "#Hds";
      iIntros "!>" (ρ Hpid%path_includes_field_aliases) "#Hg".
    rewrite def_interp_tvmem_eq path_wp_pv /=. iLöb as "IH".
    iApply clty_commute. rewrite norm_selfSubst.
    iApply ("Hds" $! (vobj _ .: ρ) with "[%] [$IH $Hg //]").
    exact: path_includes_self.
  Qed.

  Lemma D_New_Mem_I Γ T l ds:
    TAnd (TLater T) (TSing (pself (pv (ids 1)) l)) :: Γ ⊨ds ds : T -∗
    Γ ⊨ { l := dpt (pv (vobj ds)) } : TVMem l (TMu T).
  Proof. apply sD_New_Mem_I. Qed.

  (* Check that Löb induction works as expected for proving introduction of
   * objects. Using Löb induction works easily.
   *
   * Γ, x: ▷ T ⊨ ds : T
   * ---------------------
   * Γ ⊨ nu x. ds : μ x. T
   *)
  Lemma sT_Obj_I (Γ : sCtx Σ) (T : clty Σ) ds:
     oLater T :: Γ s⊨ds ds : T -∗
     Γ s⊨ tv (vobj ds) : oMu T.
  Proof.
    iDestruct 1 as (Hwf) "#Hds"; iIntros "!>" (ρ) "#Hg /= !>".
    rewrite -wp_value' /=. iLöb as "IH".
    iApply clty_commute. rewrite norm_selfSubst.
    iApply ("Hds" $! (vobj _ .: ρ) with "[%] [$IH $Hg]").
    exact: path_includes_self.
  Qed.

  Lemma T_Obj_I Γ T ds:
     Γ |L T ⊨ds ds : T -∗
     Γ ⊨ tv (vobj ds) : TMu T.
  Proof. apply sT_Obj_I. Qed.

  Lemma sD_Nil Γ : Γ s⊨ds [] : cTop.
  Proof. by iSplit; last iIntros "!> **". Qed.

  Lemma D_Nil Γ : Γ ⊨ds [] : TTop.
  Proof. apply sD_Nil. Qed.

  Lemma sD_Cons Γ d ds l (T1 T2 : cltyO Σ):
    dms_hasnt ds l →
    Γ s⊨ { l := d } : T1 -∗ Γ s⊨ds ds : T2 -∗
    Γ s⊨ds (l, d) :: ds : cAnd T1 T2.
  Proof.
    iIntros (Hlds) "#HT1 [% #HT2]"; iSplit.
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
