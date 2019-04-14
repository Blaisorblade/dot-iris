From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import weakestpre lifting.
From iris.program_logic Require Import language.
From D Require Import tactics proofmode_extra.
From D.DSub Require Import rules synLemmas step_fv.
From D.DSubSyn Require Import unary_lr_binding.

Import uPred.

Implicit Types (L T U: ty) (v: vl) (e: tm) (Γ : ctx).

Section Sec.
  Context `{!dsubSynG Σ}.

  Lemma wp_wand_cl e Φ Ψ:
    WP e {{ v, Φ v }} -∗ ⌜ nclosed e 0 ⌝ -∗ (∀ v, Φ v -∗ ⌜ nclosed_vl v 0 ⌝ -∗ Ψ v) -∗ WP e {{ v, Ψ v }}.
  Proof.
    iIntros "/= He" (Hcle) "Himpl". iApply (wp_wand_wf _ _ e Φ (flip nclosed 0) Hcle with "He [Himpl]").
    intros. by eapply nclosed_prim_step.
    iIntros (v Hclv) "/= H". iApply ("Himpl" with "H [%]"). by apply fv_tv_inv.
  Qed.

  Lemma mlater_pers (P: iProp Σ) : □ ▷ P ⊣⊢ ▷ □ P.
  Proof. iSplit; by iIntros "#? !>!>". Qed.
  Lemma mlaterN_pers (P: iProp Σ) i : □ ▷^i P ⊣⊢ ▷^i □ P.
  Proof. iSplit; by iIntros "#? !>!>". Qed.
  Lemma mlater_impl (P Q: iProp Σ) : (▷ P → ▷ Q) ⊣⊢ ▷ (P → Q).
  Proof. iSplit. admit. iApply later_impl. Admitted.
  Lemma mlaterN_impl (P Q: iProp Σ) i : (▷^i P → ▷^i Q) ⊣⊢ ▷^i (P → Q).
  Proof. iSplit. admit. iApply laterN_impl. Admitted.

  Context {Γ}.

  Lemma T_Var x T:
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ ⊨ tv (var_vl x) : T.|[ren (+x)].
  Proof.
    iIntros (Hx) "/=". iSplit; eauto using lookup_fv. iIntros "!> * #Hg".
    iApply wp_value'.
    by iApply interp_env_lookup.
  Qed.

  Lemma T_Forall_E e1 e2 T1 T2:
    (Γ ⊨ e1: TAll T1 T2.|[ren (+1)] →
     Γ ⊨ e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
     Γ ⊨ tapp e1 e2 : T2)%I.
  Proof.
    iIntros "/= #[% #He1] #[% #Hv2]". iSplit; eauto using fv_tapp. iIntros " !> * #HG".
    smart_wp_bind (AppLCtx (e2.|[to_subst ρ])) v "#Hr" "He1".
    smart_wp_bind (AppRCtx v) w "#Hw" "Hv2".
    unfold_interp. iDestruct "Hr" as (Hclv t ->) "#Hv".
    iApply wp_pure_step_later; trivial. iNext.
    iApply wp_mono; last by iApply "Hv".
    iIntros (v0) "#H".
    by iApply (interp_weaken_one w).
  Qed.

  Lemma T_Forall_Ex e1 v2 T1 T2:
    (Γ ⊨ e1: TAll T1 T2 →
     Γ ⊨ tv v2 : T1 →
    (*────────────────────────────────────────────────────────────*)
     Γ ⊨ tapp e1 (tv v2) : T2.|[v2/])%I.
  Proof.
    iIntros "/= #[% He1] #[% Hv2Arg]". move: H H0 => Hcle1 Hclv2. iSplit; eauto using fv_tapp. iIntros " !> * #HG".
    (* iAssert (⌜ length ρ = length Γ ⌝)%I as "%". by iApply interp_env_len_agree. move: H => Hlen. *)
    iAssert (⌜ nclosed_vl v2 (length Γ) ⌝)%I as "%". by iPureIntro; apply fv_tv_inv. move: H => Hcl.
    (* assert (nclosed_vl v2 (length ρ)). by rewrite Hlen. *)
    smart_wp_bind (AppLCtx (tv v2.[to_subst ρ])) v "#Hr" "He1".
    unfold_interp. iDestruct "Hr" as (Hclv t ->) "#HvFun".
    iApply wp_pure_step_later; trivial. iNext.
    iApply wp_wand.
    - iApply "HvFun".
      iApply wp_value_inv'. by iApply "Hv2Arg".
    - iIntros (v0) "#H". by iApply (interp_subst_closed _ T2 v2 v0).
  Qed.

  Lemma T_Forall_I T1 T2 e:
    (T1.|[ren (+1)] :: Γ ⊨ e : T2 →
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2)%I.
  Proof.
    iIntros "/= #[% #HeT]". move: H => Hcle.
    iSplit; eauto using fv_tv, fv_vabs.
    iIntros " !> * #HG".
    iPoseProof (interp_env_ρ_closed with "HG") as "%". move: H => Hclρ.
    iPoseProof (interp_env_len_agree with "HG") as "%". move: H => Hlen. rewrite <- Hlen in Hcle.
    (* iAssert (⌜ length ρ = length Γ ⌝)%I as "%". by iApply interp_env_len_agree. move: H => Hlen. *)
    iApply wp_value'.
    unfold_interp.
    iSplit.
    {
      pose proof (fv_to_subst (tv (vabs e)) ρ) as Hfv.
      eauto 6 using fv_tv_inv, fv_vabs, fv_tv.
    }
    iExists _; iSplitL => //.
    iIntros "!> !>" (v) "#Hv". iSpecialize ("HeT" $! (v :: ρ)).
    (* Faster than 'asimpl'. *)
    replace (e.|[up (to_subst ρ)].|[v/]) with (e.|[to_subst (v :: ρ)]) by by asimpl.
    iApply "HeT".
    iFrame "HG".
    by iApply (interp_weaken_one v).
  Qed.

  Lemma nclosed_subst_ρ e ρ: nclosed e (length Γ) → ⟦ Γ ⟧* ρ -∗ ⌜ nclosed e.|[to_subst ρ] 0 ⌝.
  Proof.
    iIntros (Hcl) "Hg".
    iPoseProof (interp_env_ρ_closed with "Hg") as "%". move: H => Hclρ.
    iPoseProof (interp_env_len_agree with "Hg") as "%". move: H => Hlen. rewrite <- Hlen in Hcl.
    iPureIntro. by apply fv_to_subst.
  Qed.

  Lemma T_Sub e T1 T2 i:
    (Γ ⊨ e : T1 →
    Γ ⊨ [T1, 0] <: [T2, i] →
    (*───────────────────────────────*)
    Γ ⊨ iterate tskip i e : T2)%I.
  Proof.
    iIntros "/= * #[% #HeT1] #Hsub". move: H => Hcle.
    have Hclte: nclosed (iterate tskip i e) (length Γ) by eauto using nclosed_tskip_i. iFrame "%".
    move: Hclte => _. iIntros "!> * #Hg".
    rewrite tskip_subst tskip_n_to_fill. iApply wp_bind.
    iApply (wp_wand_cl _ (⟦ T1 ⟧ ρ)) => //.
    - iApply ("HeT1" with "[//]").
    - by iApply nclosed_subst_ρ.
    - iIntros (v) "#HvT1"; iIntros (Hclv). rewrite -tskip_n_to_fill.
      iApply wp_pure_step_later; trivial.
      (* We can swap ▷^i with WP (tv v)! *)
      iApply wp_value; by iApply "Hsub".
  Qed.

  Lemma DT_Sub e T1 T2 i:
    (Γ ⊨ e : T1 →
    Γ ⊨[0] T1 <: iterate TLater i T2 →
    (*───────────────────────────────*)
    Γ ⊨ iterate tskip i e : T2)%I.
  Proof.
    iIntros "/= * #[% #HeT1] #Hsub". move: H => Hcle.
    have Hclte: nclosed (iterate tskip i e) (length Γ) by eauto using nclosed_tskip_i. iFrame "%".
    move: Hclte => _. iIntros "!> * #Hg".
    rewrite tskip_subst tskip_n_to_fill. iApply wp_bind.
    iApply (wp_wand_cl _ (⟦ T1 ⟧ ρ)) => //.
    - iApply ("HeT1" with "[//]").
    - by iApply nclosed_subst_ρ.
    - iIntros (v) "#HvT1"; iIntros (Hclv). rewrite -tskip_n_to_fill.
      iApply wp_pure_step_later; trivial.
      iSpecialize ("Hsub" with "Hg HvT1").
      rewrite iterate_TLater_later; last done.
      (* We can swap ▷^i with WP (tv v)! *)
      iApply wp_value. by iApply "Hsub".
  Qed.

  Lemma T_Vty_abs_I T L U :
    nclosed T (length Γ) →
    Γ ⊨ [T, 1] <: [U, 1] -∗
    Γ ⊨ [L, 1] <: [T, 1] -∗
    Γ ⊨ tv (vty T) : TTMem L U.
  Proof.
    (* Ltac solve_fv_congruence := rewrite /nclosed /nclosed_vl /= => *; f_equiv; solve [(idtac + asimpl); auto using eq_up]. *)
    iIntros (HclT) "#HTU #HLT /=".
    have HclV: nclosed_vl (vty T) (length Γ). by apply fv_vty.
    have HclTV: nclosed (tv (vty T)) (length Γ). by apply fv_tv.
    iSplit => //.
    iIntros "!>" (ρ) "#HG".
    iApply wp_value.
    unfold_interp.
    iPoseProof (interp_env_ρ_closed with "HG") as "%". move: H => Hclρ.
    iPoseProof (interp_env_len_agree with "HG") as "%". move: H => Hlen. rewrite <- Hlen in *.
    iSplit. {
      iPureIntro; by apply (fv_to_subst_vl (vty T) ρ).
    }
    iExists (λ v, ⟦ T.|[to_subst ρ ] ⟧ [] v)%I.
    iSplit. by iExists (T.|[to_subst ρ ]).
    iModIntro; repeat iSplitL; iIntros "*".
    - iIntros (Hclv) "#HL /=".
      iSpecialize ("HLT" $! ρ v Hclv with "HG HL"). iNext.
      by rewrite interp_subst_all.
    - iIntros; iApply "HTU" => //; iNext => //.
      by rewrite interp_subst_all.
  Qed.

  Lemma DT_Vty_abs_I T L U :
    nclosed T (length Γ) →
    Γ ⊨[1] T <: U -∗
    Γ ⊨[1] L <: T -∗
    Γ ⊨ tv (vty T) : TTMem L U.
  Proof.
    (* Ltac solve_fv_congruence := rewrite /nclosed /nclosed_vl /= => *; f_equiv; solve [(idtac + asimpl); auto using eq_up]. *)
    iIntros (HclT) "#HTU #HLT /=".
    have HclV: nclosed_vl (vty T) (length Γ). by apply fv_vty.
    have HclTV: nclosed (tv (vty T)) (length Γ). by apply fv_tv.
    iSplit => //.
    iIntros "!>" (ρ) "#HG".
    iApply wp_value.
    unfold_interp.
    iPoseProof (interp_env_ρ_closed with "HG") as "%". move: H => Hclρ.
    iPoseProof (interp_env_len_agree with "HG") as "%". move: H => Hlen. rewrite <- Hlen in *.
    iSplit. {
      iPureIntro; by apply (fv_to_subst_vl (vty T) ρ).
    }
    iExists (λ v, ⟦ T.|[to_subst ρ ] ⟧ [] v)%I.
    iSplit. by iExists (T.|[to_subst ρ ]).
    iModIntro; repeat iSplitL; iIntros "*".
    - iIntros (Hclv) "#HL /=".
      iSpecialize ("HLT" $! ρ with "HG HL"). iNext.
      by rewrite interp_subst_all.
    - iIntros; iApply "HTU" => //; iNext => //.
      by rewrite interp_subst_all.
  Qed.

  Lemma Sub_Sel L U va i:
    Γ ⊨ tv va : TTMem L U, i -∗
    Γ ⊨ [L, S i] <: [TSel va, i].
  Proof.
    iIntros "/= #[% #Hva] !> *" (Hclv) " #Hg #HvL". move: H => Hclva.
    iSpecialize ("Hva" $! ρ with "Hg"). iNext.
    iPoseProof (wp_value_inv' with "Hva") as "Hva'";  iClear "Hva".
    unfold_interp.
    iDestruct "Hva'" as (Hclvas φ) "#[H1 #[HLφ HφU]]".
    iDestruct "H1" as (T) "[% Hφ]".
    repeat iSplit => //.
    iExists φ. repeat iSplit. naive_solver.
    by iApply "HLφ".
  Qed.

  Lemma DSub_Sel L U va i:
    Γ ⊨ tv va : TTMem L U, i -∗
    Γ ⊨[i] TLater L <: TSel va.
  Proof.
    iIntros "/= #[% #Hva] !> * #Hg". move: H => Hclva.
    iSpecialize ("Hva" $! ρ with "Hg"). iNext.
    setoid_unfold_interp.
    iIntros (v) " #[% HvL]". move: H => Hclv.
    iPoseProof (wp_value_inv' with "Hva") as "Hva'"; iClear "Hva".
    unfold_interp.
    iDestruct "Hva'" as (Hclvas φ) "#[H1 #[HLφ HφU]]".
    iDestruct "H1" as (T) "[% Hφ]".
    repeat iSplit => //.
    iExists φ. repeat iSplit. naive_solver.
    by iApply "HLφ".
  Qed.

  Lemma Sel_Sub L U va i:
    Γ ⊨ tv va : TTMem L U, i -∗
    Γ ⊨ [TSel va, i] <: [U, S i].
  Proof.
    iIntros "/= #[% #Hva] !> *" (Hclv) "#Hg #Hφ". move: H => Hclva.
    iSpecialize ("Hva" $! ρ with "Hg").
    rewrite -swap_later.
    iNext i.
    iPoseProof (wp_value_inv' with "Hva") as "Hva'";  iClear "Hva".
    unfold_interp.
    iDestruct "Hva'" as (Hclvas φ) "#[HT0 #[HLφ HφU]]".
    iDestruct "Hφ" as "[_ Hφ]".
    iDestruct "Hφ" as (φ1) "[HT1 #Hφ1v]".
    iApply "HφU" => //.

    (* To conclude, show that both types fetched from va coincide - but later! *)
    iPoseProof (vl_has_semtype_agree with "HT0 HT1") as "Hag".
    iNext. by iRewrite ("Hag" $! v).
  Qed.

  Lemma T_Nat_I n:
    Γ ⊨ tv (vnat n): TNat.
  Proof.
    iSplit => //.
    iIntros "/= !>" (ρ) "Hg".
    iApply wp_value. unfold_interp. by iExists n.
  Qed.

  Lemma Sub_Index_Incr T U i j:
    (Γ ⊨ [T, i] <: [U, j] →
     Γ ⊨ [T, S i] <: [U, S j])%I.
  Proof. iIntros "/= #Hsub !> ** !>". by iApply "Hsub". Qed.

  Lemma Sub_TAllConCov T1 T2 U1 U2 i:
    Γ ⊨ [ T2, i ] <: [ T1, i ] -∗
    iterate TLater i T2.|[ren (+1)] :: Γ ⊨ [ U1, i ] <: [ U2, i ] -∗
    Γ ⊨ [ TAll T1 U1, i ] <: [ TAll T2 U2, i ].
  Proof.
    iIntros "#IHT #IHT1 /= !>" (ρ v Hcl) "#Hg".
    unfold_interp.
    iIntros "[$ #HT1]".
    iDestruct "HT1" as (t) "#[Heq #HT1']".
    iExists t; iSplit => //.
    rewrite -!mlaterN_pers.
    iDestruct "HT1'" as "#HT1"; iModIntro.
    iIntros (w).
    rewrite -mlater_impl -mlaterN_impl !swap_later.
    iIntros "#HwT2"; iNext 1.
    iAssert (▷^i ⌜ nclosed_vl w 0 ⌝)%I as "#Hlclw".
    by iNext; iApply interp_v_closed.
    (* Not sure how easy is this to fix??? If
    it's possible at all? Maybe with except-0,
    but we must strip *i+1* laters!
    Or by using the alternative subtyping judgment.
    *)
    have Hclw: nclosed_vl w 0. admit.
    (* Alternative: investigate how forall
    commutes with later, and see if that lets us anticipate
    pure hypotheses.*)

    iSpecialize ("IHT" $! ρ w Hclw with "Hg HwT2").

    (* iSpecialize ("IHT1" $! (w :: ρ)). *)
    iAssert (□ ▷^i (∀ v0, ⌜ nclosed_vl v0 0 ⌝ →
      ⟦ U1 ⟧ (w :: ρ) v0 → ⟦ U2 ⟧ (w :: ρ) v0))%I as "#IHT1'". {
      iIntros "!>" (v0 Hclv0).
      rewrite -!mlaterN_impl.
      iApply ("IHT1" $! (w :: ρ) v0 Hclv0 with "[#]").
      iFrame "Hg".
      rewrite iterate_TLater_later //.
      by iApply interp_weaken_one.
    }
    iClear "IHT1".
    (* rewrite laterN_impl. *)
    iSpecialize ("HT1" $! w with "IHT").
    iNext i.
    iApply (wp_wand_cl (t.|[w/]) (⟦ U1 ⟧ (w :: ρ)) (⟦ U2 ⟧ (w :: ρ)) with "HT1").
    - iDestruct "Heq" as "%"; subst.
      iPureIntro; apply nclosed_subst; by [|apply fv_vabs_inv].
    - iIntros. by iApply "IHT1'".
  Admitted.

  Lemma DSub_TAll_Variant T1 T2 U1 U2 i:
    Γ ⊨[S i] T2 <: T1 -∗
    iterate TLater (S i) T2.|[ren (+1)] :: Γ ⊨[S i] U1 <: U2 -∗
    Γ ⊨[i] TAll T1 U1 <: TAll T2 U2.
  Proof.
    rewrite iterate_S /=.
    setoid_unfold_interp.
    iIntros "#HsubT #HsubU /= !>" (ρ) "#Hg".
    iIntros (v).
    iSpecialize ("HsubT" with "Hg").
    iAssert (□∀ w, ⌜nclosed_vl w 0⌝ -∗ ▷^(S i) ⟦ T2.|[ren (+1)]⟧ (w :: ρ) w -∗ ▷ ▷^i(∀ v, ⟦ U1 ⟧ (w :: ρ) v → ⟦ U2 ⟧ (w :: ρ) v))%I as "#HsubU'".
    by iIntros "!>" (w Hclw) "#Hw"; iApply "HsubU"; unfold_interp; rewrite iterate_TLater_later //; iFrame "#%". iClear "HsubU".

    (* iAssert (□∀ w, ⌜nclosed_vl w 0⌝ -∗ ▷^(S i) (⟦ T2.|[ren (+1)]⟧ (w :: ρ) w → ∀ v, ⟦ U1 ⟧ (w :: ρ) v → ⟦ U2 ⟧ (w :: ρ) v))%I as "#HsubU''".
    iIntros "!>" (w Hclw).
    iSpecialize ("HsubU'" $! w Hclw). iNext. iNext.
    iIntros "#Hw" (u) "#Hu". Fail iApply "HsubU". *)

    unfold_interp.
    rewrite -mlaterN_impl.
    iIntros "[$ #HT1]".
    iDestruct "HT1" as (t) "#[Heq #HT1]"; iExists t; iSplit => //.
    iIntros (w).
    iSpecialize ("HT1" $! w).
    iSpecialize ("HsubT" $! w).
    rewrite -!mlaterN_pers -!laterN_later/= -!mlaterN_impl -!mlater_impl.
    iIntros "!> #HwT2".
    iAssert (▷ ▷^i ⌜ nclosed_vl w 0 ⌝)%I as "#Hlclw".
    by iNext; iNext; iApply interp_v_closed.
    have Hclw: nclosed_vl w 0. admit.

    iSpecialize ("HT1" with "[#]"). by iApply "HsubT".
    iSpecialize ("HsubU'" $! w Hclw with "[#]").
    by iApply interp_weaken_one.
    iNext; iNext i.
    iApply wp_wand.
    - iApply ("HT1").
    - iIntros (u) "#HuU1". by iApply "HsubU'".
  Admitted.

  Lemma Sub_TTMem_Variant L1 L2 U1 U2 i:
    Γ ⊨ [L2, S i] <: [L1, S i] -∗
    Γ ⊨ [U1, S i] <: [U2, S i] -∗
    Γ ⊨ [TTMem L1 U1, i] <: [TTMem L2 U2, i].
  Proof.
    iIntros "#IHT #IHT1 /= !>" (ρ v Hcl) "#Hg".
    unfold_interp.
    iIntros "[$ #HT1]".
    iDestruct "HT1" as (φ) "#[Hφl [HLφ #HφU]]".
    setoid_rewrite <- later_laterN.
    setoid_rewrite mlaterN_impl.
    iExists φ; repeat iSplitL; first done;
      rewrite -!mlaterN_pers;
      iIntros "!>" (w Hclw);
      iSpecialize ("IHT" $! ρ w Hclw with "Hg");
      iSpecialize ("IHT1" $! ρ w Hclw with "Hg");
      iNext; iIntros.
    - iApply "HLφ" => //. by iApply "IHT".
    - iApply "IHT1". by iApply "HφU".
  Qed.
  (* Lemma DSub_TTMem_Variant L1 L2 U1 U2 i:
    Γ ⊨[S i] L2 <: L1 -∗
    Γ ⊨[S i] U1 <: U2 -∗
    Γ ⊨[i] TTMem L1 U1 <: TTMem L2 U2. *)
End Sec.

From D.DSubSyn Require Import typing.

Section Fundamental.
  Context `{!dsubSynG Σ}.

  Lemma fundamental_subtype Γ T1 i1 T2 i2 (HT: Γ ⊢ₜ T1, i1 <: T2, i2):
    Γ ⊨ [T1, i1] <: [T2, i2]
  with
  fundamental_typed Γ e T (HT: Γ ⊢ₜ e : T):
    Γ ⊨ e : T.
  Proof.
    - iInduction HT as [] "IHT".
      + by iApply Sub_Refl.
      + by iApply Sub_Trans.
      + by iIntros "!> **".
      (* + by iApply Sub_Later.
      + by iApply Sub_Mono. *)
      + by iApply Sub_Index_Incr.
      + iApply Sel_Sub. by iApply fundamental_typed.
      + iApply Sub_Sel. by iApply fundamental_typed.
      + by iApply Sub_TAllConCov.
      + by iApply Sub_TTMem_Variant.
    - iInduction HT as [] "IHT".
      + by iApply T_Forall_Ex.
      + by iApply T_Forall_E.
      + by iApply T_Forall_I.
      (* + iApply T_New_I.
        by iApply fundamental_dms_typed.
      + by iApply TMu_I. *)
      + by iApply T_Nat_I.
      + by iApply T_Var.
      + iApply T_Sub => //.
        by iApply fundamental_subtype.
  Qed.
End Fundamental.

From D.pure_program_logic Require Import adequacy.

Theorem adequacy Σ `{HdsubG: dsubSynG Σ} e e' thp σ σ' T:
  (forall `{dsubSynG Σ}, True ⊢ [] ⊨ e : T) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hlog ??. cut (adequate NotStuck e σ (λ _ _, True)); first (intros [_ ?]; eauto).
  eapply (wp_adequacy Σ) => /=.
  iIntros (?) "!>". iExists (λ _ _, True%I); iSplit=> //.
  iPoseProof (Hlog with "[//]") as "#[_ #Hlog]".
  iEval (replace e with (e.|[to_subst []]) by by asimpl).
  iApply wp_wand; by [iApply "Hlog" | auto].
Qed.

Instance dsubSynG_empty: dsubSynG #[].

Corollary type_soundness e e' thp σ σ' T:
  ([] ⊢ₜ e : T) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros HT Heval.
  eapply (adequacy #[]); last done.
  iIntros; by iApply (fundamental_typed _ _ _ HT).
Qed.
