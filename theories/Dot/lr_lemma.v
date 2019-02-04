From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre.

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

From iris.program_logic Require Import lifting language ectx_lifting.
From D Require Import tactics.
From D.Dot Require Import rules synLemmas unary_lr_binding.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).
Section Sec.
  Context `{HdotG: dotG Σ} Γ.

  Lemma wp_wand_cl e Φ Ψ:
    (WP e {{ v, Φ v }} -∗ ⌜ nclosed e 0 ⌝ -∗ (∀ v, Φ v -∗ ⌜ nclosed_vl v 0 ⌝ -∗ Ψ v) -∗ WP e {{ v, Ψ v }})%I.
  Admitted.

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

  Lemma nclosed_tskip_i e n i:
    nclosed e n →
    nclosed (iterate tskip i e) n.
  Proof.
    move => Hcl; elim: i => [|i IHi]; rewrite ?iterate_0 ?iterate_S //; solve_fv_congruence.
  Qed.

  Lemma tskip_n_to_fill i e: iterate tskip i e = fill (repeat SkipCtx i) e.
  Proof. elim: i e => [|i IHi] e //; by rewrite ?iterate_0 ?iterate_Sr /= -IHi. Qed.
  Lemma tskip_subst i e s: (iterate tskip i e).|[s] = iterate tskip i e.|[s].
  Proof. elim: i => [|i IHi]; by rewrite ?iterate_0 ?iterate_S //= IHi. Qed.

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
    - iApply ("HeT1" $! ρ with "Hg").
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
    iSpecialize ("HT" $! ρ with "HG").
    rewrite iterate_S.
    smart_wp_bind SkipCtx v "#[% Hr]" "HT".
    iApply wp_pure_step_later; auto.
    iNext. by iApply wp_value.
  Qed.

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

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂
     ----------------------------------------------- (<:-Mu-1)
     Γ ⊨ μ (x: T₁ˣ) <: T₂
  *)

  Lemma Sub_Mu_1 T1 T2 i j:
    (iterate TLater i T1 :: Γ ⊨ [T1, i] <: [T2.|[ren (+1)], j] →
     Γ ⊨ [TMu T1, i] <: [T2, j])%I.
  Proof.
    iIntros "/= #Hstp !> * % #Hg #HT1".
    iApply (interp_weaken_one v).
    iApply ("Hstp" $! (v :: ρ)); rewrite ?iterate_TLater_later //; by iSplit.
  Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ <: T₂ᶻ
     ----------------------------------------------- (<:-Bind-2)
     Γ ⊨ T₁ <: μ(x: T₂ˣ)
  *)
  Lemma Sub_Mu_2 T1 T2 i j:
    (iterate TLater i T1.|[ren (+1)] :: Γ ⊨ [T1.|[ren (+1)], i] <: [T2, j] →
    Γ ⊨ [T1, i] <: [TMu T2, j])%I.
  Proof.
    iIntros "/= #Hstp !> * % #Hg #HT1".
    rewrite -(interp_weaken_one v T1 ρ v).
    iApply ("Hstp" $! (_ :: _) _); rewrite ?iterate_TLater_later //; by iSplit.
  Qed.

  Lemma T_Forall_E e1 e2 T1 T2:
    (Γ ⊨ e1: TAll T1 T2.|[ren (+1)] →
     Γ ⊨ e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
     Γ ⊨ tapp e1 e2 : T2)%I.
  Proof.
    iIntros "/= #[% He1] #[% Hv2]". iSplit; eauto using fv_tapp. iIntros " !> * #HG".
    iSpecialize ("He1" with "HG"); iSpecialize ("Hv2" with "HG").
    smart_wp_bind (AppLCtx (e2.|[to_subst ρ])) v "#Hr" "He1".
    smart_wp_bind (AppRCtx v) w "#Hw" "Hv2".
    iDestruct "Hr" as (Hclv t ->) "#Hv".
    iApply wp_pure_step_later; trivial. iNext.
    iApply wp_mono; [|iApply "Hv"]; auto.
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
    (* iAssert (⌜ length ρ = length Γ ⌝)%I as "%". by iApply interp_env_len_agree. move: H => Hlen. *)
    iAssert (⌜ nclosed_vl v2 (length Γ) ⌝)%I as "%". by iPureIntro; apply fv_tv_inv. move: H => Hcl.
    (* assert (nclosed_vl v2 (length ρ)). by rewrite Hlen. *)
    iSpecialize ("He1" with "HG"); iSpecialize ("Hv2Arg" with "HG").
    smart_wp_bind (AppLCtx (tv v2.[to_subst ρ])) v "#Hr" "He1".
    iDestruct "Hr" as (Hclv t ->) "#HvFun".
    iApply wp_pure_step_later; trivial. iNext.
    iApply wp_wand.
    - iApply fupd_wp.
      iApply "HvFun".
      iApply wp_value_inv'; by iApply "Hv2Arg".
    - iIntros (v0) "#H". by iApply (interp_subst_closed _ T2 v2 v0).
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
    replace (e.|[up (to_subst ρ)].|[v/]) with (e.|[to_subst (v :: ρ)]) by by asimpl.
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

  (* BEWARE NONSENSE IN NOTES:
     Γ ⊨ x: Tˣ
     ----------------------------------------------- (<:)
     Γ ⊨ mu(x: Tˣ) <: Tˣ    Γ ⊨ Tˣ <: mu(x: Tˣ)

     Luckily we don't need that, all the rules that exist before appear reasonable. *)

  (*
     Γ ⊨ z: Tᶻ
     =============================================== (T-Rec-I/T-Rec-E)
     Γ ⊨ z: mu(x: Tˣ)
   *)
  Lemma ivstp_rec_eq T v:
    (ivtp Γ (TMu T) v ∗-∗
    ivtp Γ T.|[v/] v)%I.
  Proof.
    iSplit; iIntros "/= #[% #Htp]"; iSplit => //; iIntros " !> * #Hg";
    iApply interp_subst_closed => //; by iApply "Htp".
  Qed.

  Lemma ivstp_rec_i T v:
    ((∀ ρ1 ρ2, (∀ x, x < length Γ → ρ1 x = ρ2 x) → v.[ρ1] = v.[ρ2]) ->
    ivtp Γ T.|[v/] v -∗
    ivtp Γ (TMu T) v).
  Proof. by intros; iDestruct ivstp_rec_eq as "[? ?]". Qed.

  Lemma ivstp_rec_e T v:
    ((∀ ρ1 ρ2, (∀ x, x < length Γ → ρ1 x = ρ2 x) → v.[ρ1] = v.[ρ2]) ->
    ivtp Γ (TMu T) v -∗
    ivtp Γ T.|[v/] v).
  Proof. by intros; iDestruct ivstp_rec_eq as "[? ?]". Qed.


End Sec.
