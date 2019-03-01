From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

(** Paolo to Amin: it seems below we might need something vaguely similar to the following. Not sure they're exactly true as stated. *)
Section wp_extra.
Context `{irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* (** A variant of wp_wand that requires proof of [Φ v -∗ Ψ v] only if [v] is an evaluation result. *) *)
(* Lemma wp_wand_steps s E e Φ Ψ: *)
(*     (WP e @ s; E {{ v, Φ v }} -∗ *)
(*     (** The nsteps premise is wrong for a multithreaded program logic, feel free to use a more accurate one. *)
(*         This one might be fine for DOT. *) *)
(*     (∀ v σ1 κ σ2 i, ⌜ nsteps i ([e], σ1) κ ([of_val v], σ2) ⌝ -∗ Φ v -∗ Ψ v)-∗ *)
(*     WP e @ s; E {{ v, Ψ v }})%I. *)
(* Admitted. *)

End wp_extra.

From D Require Import tactics.
From D.Dot Require Import rules synLemmas unary_lr_binding.
From iris.program_logic Require Import ectx_language.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).
Section Sec.
  Context `{HdotG: dotG Σ} Γ.

  Lemma wp_wand_cl e Φ Ψ:
    (WP e {{ v, Φ v }} -∗ ⌜ nclosed e 0 ⌝ -∗ (∀ v, Φ v -∗ ⌜ nclosed_vl v 0 ⌝ -∗ Ψ v) -∗ WP e {{ v, Ψ v }})%I.
  Admitted.

  Lemma wp_and (P1 P2: vl → iProp Σ) e:
    ((WP e {{ P1 }} ) -∗ (WP e  {{ P2 }} ) -∗ WP e {{ v, P1 v ∧ P2 v }})%I.
  Proof.
    iLöb as "IH" forall (e).
    iIntros "H1 H2".
    iEval (rewrite !wp_unfold /wp_pre) in "H1";
    iEval (rewrite !wp_unfold /wp_pre) in "H2";
    iEval (rewrite !wp_unfold /wp_pre).
    case_match; first by auto.
    iIntros (σ1 k ks n) "#Ha".
    iDestruct ("H1" $! σ1 k ks n with "Ha") as "[$ H1]".
    iDestruct ("H2" $! σ1 k ks n with "Ha") as "[% H2]".
    iIntros (e2 σ2 efs Hstep).
    iSpecialize ("H1" $! e2 σ2 efs Hstep);
    iSpecialize ("H2" $! e2 σ2 efs Hstep).
    iNext.
    iDestruct "H1" as "[$ [H1 $]]".
    iDestruct "H2" as "[_ [H2 _]]".
    by iApply ("IH" with "H1 H2").
  Qed.

  Lemma TAnd_I e T1 T2:
    Γ ⊨ e : T1 -∗
    Γ ⊨ e : T2 -∗
    Γ ⊨ e : TAnd T1 T2.
  Proof.
    iIntros "#HT1 #HT2 /=".
    (* iDestruct "HT1" as "[% #HT1]". *) (* Works *)
    (* Fail iDestruct "HT1" as "[$ #HT1]". *)
    iDestruct "HT1" as "[$ #HT1']". iClear "HT1".
    iDestruct "HT2" as "[_ #HT2]".
    iIntros "!>" (ρ) "#Hg".
    iApply wp_and; by [> iApply "HT1'" | iApply "HT2"].
  Qed.

  Lemma nclosed_subst_ρ e ρ: nclosed e (length Γ) → ⟦ Γ ⟧* ρ -∗ ⌜ nclosed e.|[to_subst ρ] 0 ⌝.
  Proof.
    iIntros (Hcl) "Hg".
    iPoseProof (interp_env_ρ_closed with "Hg") as "%". move: H => Hclρ.
    iPoseProof (interp_env_len_agree with "Hg") as "%". move: H => Hlen. rewrite <- Hlen in Hcl.
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
      iPoseProof (interp_subst_closed Γ T2 v2 v0 with "HG") as "Heq" => //.
      by iApply (internal_eq_iff with "Heq").
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
      iPoseProof (interp_env_ρ_closed with "HG") as "%". move: H => Hclρ.
      iPoseProof (interp_env_len_agree with "HG") as "%". move: H => Hlen. rewrite <- Hlen in Hcle.
      iPureIntro.
      apply (fv_to_subst_vl (vabs _)); eauto using fv_vabs.
    }
    iExists _; iSplitL; first done.
    iIntros "!> !>" (v) "#Hv".
    iSpecialize ("HeT" $! (v :: ρ)).

    Tactic Notation "locAsimpl'" uconstr(e1) :=
      remember (e1) as __e' eqn:__Heqe';
      progress asimpl in __Heqe'; subst __e'.
    (* This retries multiple times; must lock patterns and ignore them *)
    Ltac locAsimpl :=
      repeat match goal with
      | |- context [?a.[?s]] => locAsimpl' a.[s]
      | |- context [?a.|[?s]] => locAsimpl' (a.|[s])
      end.

    locAsimpl.
    (* time locAsimpl' (e.|[up (to_subst ρ)].|[v/]). *)
    (* time locAsimpl' (e.|[to_subst (v :: ρ)]). *)
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
