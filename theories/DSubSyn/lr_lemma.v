From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import weakestpre lifting.
From iris.program_logic Require Import language.
From D Require Import tactics proofmode_extra.
From D.DSub Require Import rules synLemmas step_fv.
From D.DSubSyn Require Import unary_lr_binding.

Import uPred.

Implicit Types (L T U: ty) (v: vl) (e: tm) (Γ : ctx).

Class SwapProp (PROP: sbi) := {
  impl_later : ∀ (P Q: PROP), (▷ P → ▷ Q) ⊢ ▷ (P → Q)
}.

Lemma impl_laterN n `{SwapProp PROP} (P Q: PROP) : (▷^n P → ▷^n Q) ⊢ ▷^n (P → Q).
Proof. elim: n => [//|n IHn]. by rewrite impl_later IHn. Qed.

Section Sec.
  Context `{!dsubSynG Σ} `{!SwapProp (iPropSI Σ)}.

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
  Proof. iSplit. iApply impl_later. iApply later_impl. Qed.
  Lemma mlaterN_impl (P Q: iProp Σ) i : (▷^i P → ▷^i Q) ⊣⊢ ▷^i (P → Q).
  Proof. iSplit. iApply impl_laterN. iApply laterN_impl. Qed.

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
    Γ ⊨ e1: TAll T1 T2.|[ren (+1)] -∗
    Γ ⊨ e2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ ⊨ tapp e1 e2 : T2.
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
    Γ ⊨ e1: TAll T1 T2 -∗
    Γ ⊨ tv v2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ ⊨ tapp e1 (tv v2) : T2.|[v2/].
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
    T1.|[ren (+1)] :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
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
    Γ ⊨ e : T1 -∗
    Γ ⊨ [T1, 0] <: [T2, i] -∗
    (*───────────────────────────────*)
    Γ ⊨ iterate tskip i e : T2.
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

  Lemma T_Vty_I T L U :
    nclosed T (length Γ) →
    Γ ⊨ tv (vty T) : TTMem T T.
  Proof.
    iIntros; iApply T_Vty_abs_I => //; by iApply Sub_Refl.
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

  Lemma DT_Vty_I T L U :
    nclosed T (length Γ) →
    Γ ⊨ tv (vty T) : TTMem T T.
  Proof.
    iIntros; iApply DT_Vty_abs_I => //; by iApply DSub_Refl.
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
    Γ ⊨ [T, i] <: [U, j] -∗
    Γ ⊨ [T, S i] <: [U, S j].
  Proof. iIntros "/= #Hsub !> ** !>". by iApply "Hsub". Qed.

  Lemma Sub_TAllConCov T1 T2 U1 U2 i:
    Γ ⊨ [ T2, S i ] <: [ T1, S i ] -∗
    iterate TLater (S i) T2.|[ren (+1)] :: Γ ⊨ [ U1, S i ] <: [ U2, S i ] -∗
    Γ ⊨ [ TAll T1 U1, i ] <: [ TAll T2 U2, i ].
  Proof.
    rewrite iterate_S /=.
    iIntros "#HsubT #HsubU /= !>" (ρ v Hcl) "#Hg".
    unfold_interp.
    iIntros "[$ #HT1]".
    iDestruct "HT1" as (t) "#[Heq #HT1]". iExists t; iSplit => //.
    iIntros (w).
    rewrite -!mlaterN_pers -mlater_impl -mlaterN_impl !swap_later.
    iIntros "!> #HwT2".
    iApply (strip_pure_laterN_impl (S i) (nclosed_vl w 0)); first last.
      by iApply interp_v_closed.
    iIntros (Hclw).
    iSpecialize ("HsubT" $! ρ w Hclw with "Hg HwT2").
    iAssert (□ ▷ ▷^i (∀ v0, ⟦ U1 ⟧ (w :: ρ) v0 →
        ⟦ U2 ⟧ (w :: ρ) v0))%I as "#HsubU'". {
      iIntros (v0); rewrite -!mlaterN_impl -mlater_impl.
      iIntros "!> #HUv0".
      iApply (strip_pure_laterN_impl (S i) (nclosed_vl v0 0)); first last.
        by iApply interp_v_closed.
      iIntros (Hclv0).
      iApply ("HsubU" $! (w :: ρ) v0) => //.
      unfold_interp; rewrite iterate_TLater_later //.
      iFrame "Hg %". by iApply interp_weaken_one.
    }
    iClear "HsubU". iNext 1; iNext i. iApply wp_wand.
    - iApply "HT1". by iApply "HsubT".
    - iIntros (u) "#HuU1". by iApply "HsubU'".
  Qed.

  Lemma DSub_TAll_ConCov T1 T2 U1 U2 i:
    Γ ⊨[S i] T2 <: T1 -∗
    iterate TLater (S i) T2.|[ren (+1)] :: Γ ⊨[S i] U1 <: U2 -∗
    Γ ⊨[i] TAll T1 U1 <: TAll T2 U2.
  Proof.
    rewrite iterate_S /=.
    iIntros "#HsubT #HsubU /= !>" (ρ) "#Hg"; iIntros (v).
    unfold_interp; rewrite -mlaterN_impl.
    iIntros "[$ #HT1]".
    iDestruct "HT1" as (t) "#[Heq #HT1]"; iExists t; iSplit => //.
    iIntros (w).
    rewrite -!mlaterN_pers -!laterN_later/= -!mlaterN_impl -!mlater_impl.
    iIntros "!> #HwT2".
    iApply (strip_pure_laterN_impl (S i) (nclosed_vl w 0)); first last.
      by iApply interp_v_closed.
    iIntros (Hclw).
    iSpecialize ("HsubT" with "Hg").
    iSpecialize ("HsubU" $! (w :: ρ) with "[#]"). {
      unfold_interp; rewrite iterate_TLater_later //.
      iFrame "#%". by iApply interp_weaken_one.
    }
    iNext; iNext i. iApply wp_wand.
    - iApply "HT1". by iApply "HsubT".
    - iIntros (u) "#HuU1". by iApply "HsubU".
  Qed.

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

  Lemma Sub_Top T i:
    Γ ⊨ [T, i] <: [TTop, i].
  Proof. by iIntros "!> **"; unfold_interp. Qed.

  Lemma DSub_Top T i:
    Γ ⊨[i] T <: TTop.
  Proof.
    iIntros "!> ** !> **"; unfold_interp.
    by iApply interp_v_closed.
  Qed.

  Lemma Bot_Sub T i:
    Γ ⊨ [TBot, i] <: [T, i].
  Proof. by iIntros "!> ** !>"; unfold_interp. Qed.

  Lemma DBot_Sub T i:
    Γ ⊨[i] TBot <: T.
  Proof. by iIntros "!> ** !> **"; unfold_interp. Qed.
End Sec.

From D.DSubSyn Require Import typing.

Section Fundamental.
  Context `{!dsubSynG Σ} `{!SwapProp (iPropSI Σ)}.

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
      + by iApply Sub_Top.
      + by iApply Bot_Sub.
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
      + iApply T_Vty_abs_I => //;
        by iApply fundamental_subtype.
      + by iApply T_Vty_I.
    Qed.
End Fundamental.

From D.pure_program_logic Require Import adequacy.

Theorem adequacy Σ `{HdsubG: dsubSynG Σ} `{!SwapProp (iPropSI Σ)} e e' thp σ σ' T:
  (forall `{dsubSynG Σ} `{SwapProp (iPropSI Σ)}, True ⊢ [] ⊨ e : T) →
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

Class CmraSwappable (A : cmraT) := {
  (* TODO cmra_extend should really be cmra_extend_sep. *)
  cmra_extend_included: ∀ n (x x': A), ✓{S n} x → x ≼ x' → ✓{n} x' → ∃ x'', ✓{S n} x'' ∧ x ≼ x'' ∧ x' ≡{n}≡ x'';
}.

(* Lemma impl_later {M : ucmraT} `{!CmraSwappable M} (P Q: uPred M) : (▷ P → ▷ Q) ⊢ ▷ (P → Q). *)
Instance SwapCmra {M : ucmraT} `{!CmraSwappable M}: SwapProp (uPredSI M).
Proof.
  split.
  unseal; split => /= -[//|n] x ? HPQ n' x' Hle ?? HP.
  specialize (HPQ (S n')); cbn in HPQ.
  edestruct (cmra_extend_included n' x x') as (x'' &?&?& Hnx'x'') => //.
  - by eapply cmra_validN_le; eauto with lia.
  - rewrite Hnx'x''. apply HPQ; eauto with lia. hnf. by rewrite -Hnx'x''.
Qed.

Instance Swappable_iResUREmpty: CmraSwappable (iResUR #[]).
Proof.
  split. rewrite /iResUR /gid /= => n x x' Hvx Hxx' Hvx'.
  exists x'; split_and! => // ??; by apply fin_0_inv.
Qed.

Corollary type_soundness e e' thp σ σ' T:
  ([] ⊢ₜ e : T) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros HT Heval.
  eapply (adequacy #[]); last done.
  iIntros; by iApply (fundamental_typed _ _ _ HT).
Qed.
