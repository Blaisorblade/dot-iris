From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

From D Require Import tactics proofmode_extra locAsimpl.
From D.Dot Require Import rules synLemmas unary_lr_binding step_fv.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).
Section Sec.
  Context `{HdotG: dotG Σ} Γ.

  Lemma wp_wand_cl e Φ Ψ:
    WP e {{ v, Φ v }} -∗ ⌜ nclosed e 0 ⌝ -∗ (∀ v, Φ v -∗ ⌜ nclosed_vl v 0 ⌝ -∗ Ψ v) -∗ WP e {{ v, Ψ v }}.
  Proof.
    iIntros "/= He" (Hcle) "Himpl". iApply (wp_wand_wf _ _ e Φ (flip nclosed 0) Hcle with "He [Himpl]").
    intros. by eapply nclosed_prim_step.
    iIntros (v Hclv) "/= H". iApply ("Himpl" with "H [%]"). by apply fv_tv_inv.
  Qed.

  Lemma Sub_TAll_Variant T1 T2 U1 U2 i:
    ▷^(S i) (Γ ⊨ [T2, 0] <: [T1, 0]) -∗
    ▷^(S i) (T2.|[ren (+1)] :: Γ ⊨ [U1, 0] <: [U2, 0]) -∗
    ▷^i (Γ ⊨ [TAll T1 U1, 0] <: [TAll T2 U2, 0]).
  Proof.
    iIntros "#HsubT #HsubU /= !>!>" (ρ v Hcl) "#Hg [$ #HT1]".
    iDestruct "HT1" as (t) "#[Heq #HT1]"; iExists t; iSplit => //.
    iIntros (w) "!>!> #HwT2". iApply wp_wand.
    - iApply "HT1". iApply "HsubT" => //. by iApply interp_v_closed.
    - iIntros (u) "#HuU1".
      iApply ("HsubU" $! (w :: ρ) u with "[#] [#] [//]").
      by iApply interp_v_closed.
      iFrame "Hg". by iApply interp_weaken_one.
  Qed.

  Lemma TAnd_I v T1 T2:
    Γ ⊨ tv v : T1 -∗
    Γ ⊨ tv v : T2 -∗
    Γ ⊨ tv v : TAnd T1 T2.
  Proof.
    iIntros "#HT1 #HT2 /=".
    (* iDestruct "HT1" as "[% #HT1]". *) (* Works *)
    (* Fail iDestruct "HT1" as "[$ #HT1]". *)
    iDestruct "HT1" as "[$ #HT1']". iClear "HT1".
    iDestruct "HT2" as "[_ #HT2]".
    iIntros "!>" (ρ) "#Hg".
    iApply wp_and_val; by [> iApply "HT1'" | iApply "HT2"].
  Qed.


  (* Is it true that for covariant F, F[A ∧ B] = F[A] ∧ F[B]?
    Dotty assumes that, tho DOT didn't capture it.
    F[A ∧ B] <: F[A] ∧ F[B] is provable by covariance.
    Let's prove F[A] ∧ F[B] <: F[A ∧ B] in the model.
    *)
  Lemma Sub_TAll_Cov_Distr T U1 U2 i:
    Γ ⊨ [TAnd (TAll T U1) (TAll T U2), i] <: [TAll T (TAnd U1 U2), i].
  Proof.
    iIntros "/= !>" (ρ v Hcl) "#Hg [[$ #H1] #[_ H2]]". iNext.
    iDestruct "H1" as (t Heq) "#H1"; iDestruct "H2" as (t' ->) "#H2"; cinject Heq.
    iExists _; iSplit => //.
    iIntros "!>!>" (w) "#HT".
    iApply wp_and. by iApply "H1". by iApply "H2".
  Qed.

  Lemma Sub_TVMem_Cov_Distr l T1 T2 i:
    Γ ⊨ [TAnd (TVMem l T1) (TVMem l T2), i] <: [TVMem l (TAnd T1 T2), i].
  Proof.
    iIntros "/= !>" (ρ v Hcl) "#Hg [[$ #H1] #[_ H2]]". iNext.
    iDestruct "H1" as (d?? vmem?) "#H1"; iDestruct "H2" as (d'?? vmem'?) "#H2". objLookupDet; subst; injectHyps.
    repeat (iExists _; repeat iSplit => //).
  Qed.

  Lemma Sub_TVMem_Cov_Distr_2 l T1 T2 i:
    Γ ⊨ [TVMem l (TAnd T1 T2), i] <: [TAnd (TVMem l T1) (TVMem l T2), i].
  Proof.
    iIntros "/= !>" (ρ v Hcl) "#Hg [$ #H]". iNext.
    iDestruct "H" as (d?? vmem?) "#[H1 H2]".
    iSplit; repeat (iExists _; repeat iSplit => //).
  Qed.

  (* This should also follows internally from covariance, once that's proven. *)
  Lemma Sub_TVMem_Cov_Distr_Or_1 l T1 T2 i:
    Γ ⊨ [TOr (TVMem l T1) (TVMem l T2), i] <: [TVMem l (TOr T1 T2), i].
  Proof.
    iIntros "/= !>" (ρ v Hcl) "#Hg [[$ #H]| [$ #H]]"; iNext;
    iDestruct "H" as (d?? vmem?) "#H";
    repeat (iExists _; repeat iSplit => //); by [iLeft | iRight].
  Qed.

  Lemma Sub_TVMem_Cov_Distr_Or_2 l T1 T2 i:
    Γ ⊨ [TVMem l (TOr T1 T2), i] <: [TOr (TVMem l T1) (TVMem l T2), i].
  Proof.
    iIntros "/= !>" (ρ v Hcl) "#Hg [$ #H]". iNext.
    iDestruct "H" as (d?? vmem?) "#[H | H]"; [> iLeft | iRight];
      repeat (iExists _; repeat iSplit => //).
  Qed.

  Lemma Sub_TTMem_Cov_Distr l L U1 U2 i:
    Γ ⊨ [TAnd (TTMem l L U1) (TTMem l L U2), i] <: [TTMem l L (TAnd U1 U2), i].
  Proof.
    iIntros "/= !>" (ρ v Hcl) "#Hg [[$ #H1] #[_ H2]]". iNext.
    iDestruct "H1" as (d?? φ) "#[Hsφ1 #[HLφ1 HφU1]]"; iDestruct "H2" as (d'?? φ') "#[Hsφ2 #[HLφ2 HφU2]]".
    objLookupDet; subst; injectHyps.
    iExists d; repeat iSplit => //.
    iExists φ; repeat iSplit => //.
    iModIntro; iSplitL; iIntros (w Hclw) "#Hw".
    - by iApply "HLφ1".
    - iPoseProof (stored_pred_agree d _ _ w with "Hsφ1 Hsφ2") as "#Hag"; iClear "Hsφ2".
      iAssert (▷ □ φ' w)%I as "#Hw'". by iNext; iRewrite -"Hag".
      iSpecialize ("HφU1" $! w Hclw with "Hw").
      iSpecialize ("HφU2" $! w Hclw with "Hw'").
      by iFrame "HφU1 HφU2".
  Qed.

  Lemma nclosed_subst_ρ e ρ: nclosed e (length Γ) → ⟦ Γ ⟧* ρ -∗ ⌜ nclosed e.|[to_subst ρ] 0 ⌝.
  Proof.
    iIntros (Hcl) "HG".
    iDestruct (interp_env_ρ_closed with "HG") as %Hclp.
    iDestruct (interp_env_len_agree with "HG") as %Hlen. rewrite <- Hlen in *.
    iPureIntro. by apply fv_to_subst.
  Qed.

  Lemma semantic_typing_uniform_step_index T e i:
    (Γ ⊨ e : T → Γ ⊨ e : T, i)%I.
  Proof.
    iIntros "[% #H]"; move: H => Hcl; iFrame "%". iIntros " !>" (ρ) "#HΓ".
    iInduction i as [|i] "IHi". by iApply "H".
    rewrite iterate_S /=.
    iApply (wp_wand_cl (e.|[to_subst ρ]) (⟦ iterate TLater i T ⟧ ρ) _) => //.
    - by iApply nclosed_subst_ρ.
    - naive_solver.
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

  Lemma T_Var x T:
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ ⊨ tv (var_vl x) : T.|[ren (+x)].
  Proof.
    iIntros (Hx) "/=". iSplit; eauto using lookup_fv. iIntros "!> * #Hg".
    iApply wp_value'.
    by iApply interp_env_lookup.
  Qed.

  Lemma T_Skip e T i:
    (Γ ⊨ e : T, S i →
     Γ ⊨ tskip e : T, i)%I.
  Proof.
    iIntros "[% #HT]". iSplit; auto using fv_tskip. iIntros " !> * #HG".
    iSpecialize ("HT" with "[#//]").
    rewrite iterate_S.
    smart_wp_bind SkipCtx v "#[% Hr]" "HT".
    iApply wp_pure_step_later; trivial.
    iNext. by iApply wp_value.
  Qed.

  (*
     x ∉ fv T
     ----------------------------------------------- (<:)
     Γ ⊨ mu x: T <: T    Γ ⊨ T <: mu(x: T)

     Luckily we don't need that, all the rules that exist before appear reasonable. *)

  Lemma interp_TMu_ren T ρ v: ⟦ TMu T.|[ren (+1)] ⟧ ρ v ≡ ⟦ T ⟧ ρ v.
  Proof. by rewrite /= (interp_weaken_one v T ρ v). Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂ᶻ
     ----------------------------------------------- (<:-μ-X)
     Γ ⊨ μ (x: T₁ˣ) <: μ(x: T₂ˣ)
  *)
  (* Notation "◁ n T ▷" := (iterate TLater n T). *)
  Lemma Sub_Mu_X T1 T2 i j:
    (iterate TLater i T1 :: Γ ⊨ [T1, i] <: [T2, j] →
     Γ ⊨ [TMu T1, i] <: [TMu T2, j])%I.
  Proof.
    iIntros "/= #Hstp !> * % #Hg #HT1".
    iApply ("Hstp" $! (v :: ρ) _);
      rewrite ?iterate_TLater_later //; by iSplit.
  Qed.

  Lemma Sub_Mu_A T i: (Γ ⊨ [TMu T.|[ren (+1)], i] <: [T, i])%I.
  Proof. iIntros "!> *" (Hcl) "**". by rewrite (interp_TMu_ren T ρ v). Qed.

  Lemma Sub_Mu_B T i: (Γ ⊨ [T, i] <: [TMu T.|[ren (+1)], i])%I.
  Proof. iIntros "!> *" (Hcl) "**". by rewrite (interp_TMu_ren T ρ v). Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂
     ----------------------------------------------- (<:-Mu-1)
     Γ ⊨ μ (x: T₁ˣ) <: T₂
  *)

  Lemma Sub_Mu_1 T1 T2 i j:
    (iterate TLater i T1 :: Γ ⊨ [T1, i] <: [T2.|[ren (+1)], j] →
     Γ ⊨ [TMu T1, i] <: [T2, j])%I.
  Proof. iIntros "#Hstp !> * % #Hg #HT1". rewrite -(interp_TMu_ren T2 ρ v). by iApply Sub_Mu_X. Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ <: T₂ᶻ
     ----------------------------------------------- (<:-Bind-2)
     Γ ⊨ T₁ <: μ(x: T₂ˣ)
  *)
  Lemma Sub_Mu_2 T1 T2 i j:
    (iterate TLater i T1.|[ren (+1)] :: Γ ⊨ [T1.|[ren (+1)], i] <: [T2, j] →
    Γ ⊨ [T1, i] <: [TMu T2, j])%I.
  Proof. iIntros "#Hstp !> * % #Hg #HT1". rewrite -(interp_TMu_ren T1 ρ v). by iApply Sub_Mu_X. Qed.

  (* Sort-of-show this rule is derivable from Sub_Mu_X and Sub_Mu_A. *)
  Lemma Sub_Mu_1' T1 T2 i j:
    (iterate TLater i T1 :: Γ ⊨ [T1, i] <: [T2.|[ren (+1)], j] →
     Γ ⊨ [TMu T1, i] <: [T2, j])%I.
  Proof. iIntros "Hstp"; iApply (Sub_Trans with "[-] []"). by iApply Sub_Mu_X. iApply Sub_Mu_A. Qed.

  Lemma Sub_Mu_2' T1 T2 i j:
    (iterate TLater i T1.|[ren (+1)] :: Γ ⊨ [T1.|[ren (+1)], i] <: [T2, j] →
    Γ ⊨ [T1, i] <: [TMu T2, j])%I.
  Proof. iIntros "Hstp"; iApply (Sub_Trans with "[] [-]"). iApply Sub_Mu_B. by iApply Sub_Mu_X. Qed.

  (*
     Γ ⊨ z: Tᶻ
     =============================================== (T-Rec-I/T-Rec-E)
     Γ ⊨ z: mu(x: Tˣ)
   *)
  Lemma ivstp_rec_eq T v: (ivtp Γ (TMu T) v ∗-∗ ivtp Γ T.|[v/] v)%I.
  Proof.
    iSplit; iIntros "/= #[% #Htp]"; iSplit => //; iIntros " !> * #Hg";
    iPoseProof (interp_subst_closed Γ T v (v.[to_subst ρ]) with "Hg") as "H" => //;
    [ iRewrite "H" | iRewrite -"H" ]; by iApply "Htp".
  Qed.

  Lemma ivstp_rec_i T v: ivtp Γ T.|[v/] v -∗ ivtp Γ (TMu T) v.
  Proof. by intros; iDestruct ivstp_rec_eq as "[? ?]". Qed.

  Lemma ivstp_rec_e T v: ivtp Γ (TMu T) v -∗ ivtp Γ T.|[v/] v.
  Proof. by intros; iDestruct ivstp_rec_eq as "[? ?]". Qed.

  (*
     Γ ⊨ z: Tᶻ
     =============================================== (T-Rec-I/T-Rec-E)
     Γ ⊨ z: mu(x: Tˣ)
   *)
  Lemma TMu_equiv T v: (Γ ⊨ tv v : TMu T ↔ Γ ⊨ tv v : T.|[v/])%I.
  Proof.
    Import uPred.
    iSplit; iIntros "/= #[% #Htp]"; iSplit => //; iIntros " !> * #Hg"; iApply wp_value_fupd;
      (iPoseProof (interp_subst_closed Γ T v (v.[to_subst ρ]) with "[#//]") as "Heq"; first (by apply fv_tv_inv));
        iApply (internal_eq_iff with "Heq"); iSpecialize ("Htp" with "[#//]"); iApply (wp_value_inv with "Htp").
      (* Fail iRewrite "Heq". *) (* WTF *)
  Qed.

  Lemma TMu_I T v: (Γ ⊨ tv v : T.|[v/] → Γ ⊨ tv v : TMu T)%I.
  Proof. by iIntros; iApply (TMu_equiv T v). Qed.

  Lemma TMu_E T v: (Γ ⊨ tv v : TMu T → Γ ⊨ tv v : T.|[v/])%I.
  Proof. by iIntros; iApply (TMu_equiv T v). Qed.

  Lemma T_Forall_E e1 e2 T1 T2:
    (Γ ⊨ e1: TAll T1 T2.|[ren (+1)] →
     Γ ⊨ e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
     Γ ⊨ tapp e1 e2 : T2)%I.
  Proof.
    iIntros "/= #[% He1] #[% Hv2]". iSplit; eauto using fv_tapp. iIntros " !> * #HG".
    iSpecialize ("He1" with "[#//]"); iSpecialize ("Hv2" with "[#//]").
    smart_wp_bind (AppLCtx (e2.|[to_subst ρ])) v "#Hr" "He1".
    smart_wp_bind (AppRCtx v) w "#Hw" "Hv2".
    iDestruct "Hr" as (Hclv t ->) "#Hv".
    iApply wp_pure_step_later; trivial. iNext.
    iApply wp_mono; last iApply ("Hv" with "[//]").
    iIntros (v0) "#H".
    by iApply interp_weaken_one.
  Qed.

  Lemma T_Forall_Ex e1 v2 T1 T2:
    (Γ ⊨ e1: TAll T1 T2 →
     Γ ⊨ tv v2 : T1 →
    (*────────────────────────────────────────────────────────────*)
     Γ ⊨ tapp e1 (tv v2) : T2.|[v2/])%I.
  Proof.
    iIntros "/= #[% He1] #[% Hv2Arg]". move: H H0 => Hcle1 Hclv2. iSplit; eauto using fv_tapp. iIntros " !> * #HG".
    have Hcl: nclosed_vl v2 (length Γ). by apply fv_tv_inv.
    iSpecialize ("He1" with "[#//]"); iSpecialize ("Hv2Arg" with "[#//]").
    smart_wp_bind (AppLCtx (tv v2.[to_subst ρ])) v "#Hr" "He1".
    iDestruct "Hr" as (Hclv t ->) "#HvFun".
    iApply wp_pure_step_later; trivial. iNext.
    iApply wp_wand.
    - iApply "HvFun". by iApply wp_value_inv'.
    - iIntros (v0) "#H".
      by iRewrite (interp_subst_closed Γ T2 v2 v0 with "HG").
  Qed.

  (** Restricting this to index 0 appears necessary: it seems we can't swap [▷^i
      (∀ v, P v)] to [∀ v, ▷^i (P v)] (at least, tactics don't do this swap).
      We'd need this swap, and then [iIntros (v)], to specialize the hypothesis
      and drop the [▷^i] modality.*)
  Lemma T_Forall_I T1 T2 e:
    (T1.|[ren (+1)] :: Γ ⊨ e : T2 →
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2)%I.
  Proof.
    iIntros "/= #[% #HeT]". move: H => Hcle.
    iSplit; eauto using fv_tv, fv_vabs.
    iIntros " !> * #HG".
    iApply wp_value'.
    iSplit.
    {
      iDestruct (interp_env_ρ_closed with "HG") as %Hclp.
      iDestruct (interp_env_len_agree with "HG") as %Hlen. rewrite <- Hlen in *.
      iPureIntro.
      apply (fv_to_subst_vl (vabs _)); eauto using fv_vabs.
    }
    iExists _; iSplitL; first done.
    iIntros "!> !>" (v) "#Hv".
    iSpecialize ("HeT" $! (v :: ρ)).
    (* time locAsimpl. (* 10x faster than asimpl. *) *)
    (* 20x faster than asimpl. *)
    locAsimpl' (e.|[up (to_subst ρ)].|[v/]); locAsimpl' (e.|[to_subst (v :: ρ)]).
    iApply "HeT". iFrame "HG". by iApply interp_weaken_one.
  Qed.

  Lemma T_Mem_E e T l:
    (Γ ⊨ e : TVMem l T →
    (*─────────────────────────*)
    Γ ⊨ tproj e l : T)%I.
  Proof.
    iIntros "#[% HE] /=". iSplit; auto using fv_tproj. iIntros " !>" (ρ) "#HG".
    smart_wp_bind (ProjCtx l) v "#[% Hv]" "HE".
    iDestruct "Hv" as (d) "[% [% Hv]]".
    iDestruct "Hv" as (vmem) "[% Hv]".
    simplOpen ds; subst.
    match goal with H: _ @ _ ↘ _ |- _ => inversion H; ev; injectHyps end.
    iApply wp_pure_step_later; eauto.
    by iApply wp_value.
  Qed.


End Sec.
