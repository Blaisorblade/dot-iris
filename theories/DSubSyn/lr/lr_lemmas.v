(* This files contains proofs of most typing lemmas for DSub.

   This file *must not* depend on either typing.v (typing ruls) or
   swap_later_impl.v (extra swap lemmas).
 *)
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.
From D.DSub Require Import rules synLemmas.
From D.DSubSyn Require Import unary_lr.

Set Suggest Proof Using.
Set Default Proof Using "Type*".

Implicit Types (L T U: ty) (v: vl) (e: tm) (Γ : ctx).

Section Sec.
  Context `{!dsubSynG Σ} {Γ}.

  Lemma T_Var x T:
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ ⊨ tv (var_vl x) : shiftN x T.
  Proof.
    iIntros (Hx) "/= !> * #Hg".
    by rewrite -wp_value' interp_env_lookup.
  Qed.

  Lemma T_All_E e1 e2 T1 T2:
    Γ ⊨ e1: TAll T1 (shift T2) -∗
    Γ ⊨ e2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ ⊨ tapp e1 e2 : T2.
  Proof.
    iIntros "/= #He1 #Hv2 !>" (vs) "#HG".
    smart_wp_bind (AppLCtx _) v "#Hr" "He1".
    smart_wp_bind (AppRCtx v) w "#Hw" "Hv2".
    unfold_interp. iDestruct "Hr" as (t ->) "#Hv".
    rewrite -wp_pure_step_later // -wp_mono /=; first by iApply "Hv".
    iIntros (v). by rewrite (interp_weaken_one T2 _ v).
  Qed.

  Lemma T_All_Ex e1 v2 T1 T2:
    Γ ⊨ e1: TAll T1 T2 -∗
    Γ ⊨ tv v2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ ⊨ tapp e1 (tv v2) : T2.|[v2/].
  Proof.
    iIntros "/= #He1 #Hv2Arg !>" (vs) "#HG".
    smart_wp_bind (AppLCtx _) v "#Hr" "He1".
    unfold_interp. iDestruct "Hr" as (t ->) "#HvFun".
    rewrite -wp_pure_step_later; last done. iNext.
    iApply wp_wand.
    - iApply "HvFun". rewrite -wp_value_inv'. by iApply "Hv2Arg".
    - iIntros (v).
      rewrite (interp_subst_one T2 v2 v); auto.
  Qed.

  Lemma T_All_I T1 T2 e:
    shift T1 :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "/= #HeT !>" (vs) "#HG".
    rewrite -wp_value'; unfold_interp. iExists _; iSplit; first done.
    iIntros "!> !>" (v) "#Hv"; rewrite up_sub_compose.
    iApply ("HeT" $! (v .: vs) with "[$HG]").
    by rewrite (interp_weaken_one T1 _ v).
  Qed.

  Lemma T_Sub e T1 T2 i:
    Γ ⊨ e : T1 -∗
    Γ ⊨ T1, 0 <: T2, i -∗
    (*───────────────────────────────*)
    Γ ⊨ iterate tskip i e : T2.
  Proof.
    iIntros "/= * #HeT1 #Hsub !>" (vs) "#Hg".
    rewrite tskip_subst -wp_bind.
    iApply (wp_wand with "(HeT1 Hg)").
    iIntros (v) "#HvT1".
    (* We can swap ▷^i with WP (tv v)! *)
    rewrite -wp_pure_step_later // -wp_value.
    by iApply "Hsub".
  Qed.

  Lemma DT_Sub e T1 T2 i:
    Γ ⊨ e : T1 -∗
    Γ ⊨[0] T1 <: iterate TLater i T2 -∗
    (*───────────────────────────────*)
    Γ ⊨ iterate tskip i e : T2.
  Proof.
    iIntros "/= * #HeT1 #Hsub". iIntros "!>" (vs) "#Hg".
    rewrite tskip_subst tskip_n_to_fill -wp_bind.
    iApply (wp_wand with "(HeT1 Hg)").
    iIntros (v) "#HvT1".
    rewrite -tskip_n_to_fill -wp_pure_step_later //.
    iSpecialize ("Hsub" with "Hg HvT1").
    (* We can swap ▷^i with WP (tv v)! *)
    rewrite iterate_TLater_later -wp_value.
    by iApply "Hsub".
  Qed.

  Lemma T_Vty_abs_I T L U :
    Γ ⊨ T, 1 <: U, 0 -∗
    Γ ⊨ L, 0 <: T, 1 -∗
    Γ ⊨ tv (vty T) : TTMem L U.
  Proof.
    iIntros "#HTU #HLT /= !>" (vs) "#HG".
    rewrite -wp_value; unfold_interp.
    iExists _; iSplit. by iExists _.
    iModIntro; repeat iSplit; iIntros (v) "#H";
      rewrite later_intuitionistically -(interp_subst_ids _ _ _).
    - iIntros "!>"; by iApply "HLT".
    - by iApply "HTU".
  Qed.

  Lemma DT_Vty_abs_I T L U :
    Γ ⊨[0] TLater T <: U -∗
    Γ ⊨[0] L <: TLater T -∗
    Γ ⊨ tv (vty T) : TTMem L U.
  Proof.
    (* Ltac solve_fv_congruence := rewrite /nclosed /nclosed_vl /= => *; f_equiv; solve [(idtac + asimpl); auto using eq_up]. *)
    iIntros "#HTU #HLT /= !>" (ρ) "#HG".
    rewrite -wp_value; unfold_interp.
    iExists _; iSplit. by iExists _.
    iModIntro; repeat iSplit; iIntros (v) "#H";
      rewrite later_intuitionistically -(interp_subst_ids _ _ _).
    - iIntros "!>". iSpecialize ("HLT" with "HG H"). unfold_interp. iApply "HLT".
    - iApply ("HTU" with "HG"). unfold_interp. iApply "H".
  Qed.

  Lemma Sub_Sel L U va i:
    Γ ⊨ tv va : TTMem L U, i -∗
    Γ ⊨ L, i <: TSel va, i.
  Proof.
    iIntros "/= #Hva !>" (vs v) "#Hg #HvL".
    iSpecialize ("Hva" with "Hg"). iNext i.
    rewrite wp_value_inv'; unfold_interp.
    iDestruct "Hva" as (φ) "#[H1 #[HLφ HφU]]".
    iDestruct "H1" as (T) "[>% Hφ]".
    iExists φ; iSplit. naive_solver. by iApply "HLφ".
  Qed.

  Lemma DSub_Sel L U va i:
    Γ ⊨ tv va : TTMem L U, i -∗
    Γ ⊨[i] L <: TSel va.
  Proof.
    iIntros "/= #Hva !>" (vs) "#Hg".
    iSpecialize ("Hva" with "Hg"). iNext.
    iIntros (v) " #HvL".
    rewrite wp_value_inv'; unfold_interp.
    iDestruct "Hva" as (φ) "#[H1 #[HLφ HφU]]".
    iDestruct "H1" as (T) "[>% Hφ]".
    iExists φ; iSplit. naive_solver. by iApply "HLφ".
  Qed.

  Lemma Sel_Sub L U va i:
    Γ ⊨ tv va : TTMem L U, i -∗
    Γ ⊨ TSel va, i <: U, i.
  Proof.
    iIntros "/= #Hva !>" (vs v) "#Hg #Hφ".
    iSpecialize ("Hva" with "Hg").
    rewrite wp_value_inv'; unfold_interp.
    iDestruct "Hva" as (φ) "#[HT0 #[HLφ HφU]]".
    iApply "HφU".
    iDestruct "Hφ" as (φ1) "[HT1 #Hφ1v]".
    (* To conclude, show that both types fetched from va coincide - but later! *)
    iPoseProof (vl_has_semtype_agree with "HT0 HT1") as "Hag".
    iNext i. iNext. by iRewrite ("Hag" $! v).
  Qed.

  Lemma T_Nat_I n:
    Γ ⊨ tv (vint n): TInt.
  Proof.
    iIntros "/= !>" (ρ) "_". rewrite -wp_value; unfold_interp. by iExists n.
  Qed.

  Lemma Sub_Index_Incr T U i j:
    Γ ⊨ T, i <: U, j -∗
    Γ ⊨ T, S i <: U, S j.
  Proof. iIntros "/= #Hsub !> ** !>". by iApply "Hsub". Qed.

  Lemma DTyp_Sub_Typ L1 L2 U1 U2 i:
    Γ ⊨[i] L2 <: L1 -∗
    Γ ⊨[i] U1 <: U2 -∗
    Γ ⊨[i] TTMem L1 U1 <: TTMem L2 U2.
  Proof.
    iIntros "#HsubL #HsubU /= !>" (ρ) "#Hg"; iIntros (v).
    iSpecialize ("HsubL" with "Hg"); iSpecialize ("HsubU" with "Hg").
    unfold_interp. iNext.
    iDestruct 1 as (φ) "#[Hφl [#HLφ #HφU]]".
    iExists φ; repeat iSplitL; first done;
      iIntros "!>" (w) "#Hw".
    - iApply "HLφ" => //. by iApply "HsubL".
    - iApply "HsubU". by iApply "HφU".
  Qed.

  Lemma Sub_Top T i:
    Γ ⊨ T, i <: TTop, i.
  Proof. by iIntros "!> **"; unfold_interp. Qed.

  Lemma DSub_Top T i:
    Γ ⊨[i] T <: TTop.
  Proof.
    iIntros "!> ** !> **". by unfold_interp.
  Qed.

  Lemma Bot_Sub T i:
    Γ ⊨ TBot, i <: T, i.
  Proof. by iIntros "!> ** !>"; unfold_interp. Qed.

  Lemma DBot_Sub T i:
    Γ ⊨[i] TBot <: T.
  Proof. by iIntros "!> ** !> **"; unfold_interp. Qed.

  Lemma Later_Sub T i :
    Γ ⊨ TLater T, i <: T, S i.
  Proof. by iIntros "/= !> **"; unfold_interp; iNext. Qed.

  Lemma Sub_Later T i :
    Γ ⊨ T, S i <: TLater T, i.
  Proof. by iIntros "/= !> ** !>"; unfold_interp. Qed.

End Sec.
