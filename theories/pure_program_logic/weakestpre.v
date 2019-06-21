From iris.base_logic.lib Require Export fancy_updates.
From iris.program_logic Require Export language.
From iris.bi Require Export weakestpre.
From iris.proofmode Require Import base tactics classes.
Set Default Proof Using "Type".
Import uPred.

(* The following development is that of a *Plain* weakest
precondition. In the sense that it does not require any  *)

Class irisG (Λ : language) (Σ : gFunctors) := IrisG {

  (** The state interpretation is an invariant that should hold in between each
  step of reduction. Here [Λstate] is the global state, [list Λobservation] are
  the remaining observations, and [nat] is the number of forked-off threads
  (not the total number of threads, which is one higher because there is always
  a main thread). *)
  state_interp : state Λ → list (observation Λ) → nat → iProp Σ;

  (** A fixed postcondition for any forked-off thread. For most languages, e.g.
  heap_lang, this will simply be [True]. However, it is useful if one wants to
  keep track of resources precisely, as in e.g. Iron. *)
  fork_post : val Λ → iProp Σ;
}.

Definition wp_pre `{irisG Λ Σ} (s : stuckness)
    (wp : coPset -d> expr Λ -d> (val Λ -d> iProp Σ) -d> iProp Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iProp Σ) -d> iProp Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => Φ v
  | None => ∀ σ1 κ κs n,
     state_interp σ1 (κ ++ κs) n -∗
       ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
       ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗
          ▷ (state_interp σ2 κs (length efs + n) ∗
         wp E e2 Φ ∗
         [∗ list] i ↦ ef ∈ efs, wp ⊤ ef fork_post)
  end%I.

Local Instance wp_pre_contractive `{irisG Λ Σ} s : Contractive (wp_pre s).
Proof.
  rewrite /wp_pre=> n wp wp' Hwp E e1 Φ.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Definition wp_def `{irisG Λ Σ} (s : stuckness) :
  coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ := fixpoint (wp_pre s).
Definition wp_aux `{irisG Λ Σ} : seal (@wp_def Λ Σ _). by eexists. Qed.
Instance wp' `{irisG Λ Σ} : Wp Λ (iProp Σ) stuckness := wp_aux.(unseal).
Definition wp_eq `{irisG Λ Σ} : wp = @wp_def Λ Σ _ := wp_aux.(seal_eq).

Section wp.
Context `{irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma wp_unfold s E e Φ :
  WP e @ s; E {{ Φ }} ⊣⊢ wp_pre s (wp (PROP:=iProp Σ)  s) E e Φ.
Proof. rewrite wp_eq. apply (fixpoint_unfold (wp_pre s)). Qed.

Global Instance wp_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre.
  (* FIXME: figure out a way to properly automate this proof *)
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  do 21 (f_contractive || f_equiv). apply IH; first lia.
  intros v. eapply dist_le; eauto with lia.
Qed.
Global Instance wp_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.

Lemma wp_value' s E Φ v : Φ v ⊢ WP of_val v @ s; E {{ Φ }}.
Proof. iIntros "HΦ". rewrite wp_unfold /wp_pre to_of_val. auto. Qed.
Lemma wp_value_inv' s E Φ v : WP of_val v @ s; E {{ Φ }} ⊢ Φ v.
Proof. by rewrite wp_unfold /wp_pre to_of_val. Qed.

Lemma wp_strong_mono s1 s2 E1 E2 e Φ Ψ :
  s1 ⊑ s2 →
  WP e @ s1; E1 {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s2; E2 {{ Ψ }}.
Proof.
  iIntros (?) "H HΦ". iLöb as "IH" forall (e E1 E2 Φ Ψ).
  rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:?.
  { by iApply ("HΦ" with "[-]"). }
  iIntros (σ1 κ κs n) "Hσ".
  iDestruct ("H" with "[$]") as "[% H]".
  iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 efs Hstep).
  iDestruct ("H" with "[//]") as "H". iIntros "!>".
  iDestruct "H" as "(Hσ & H & Hefs)".
  iFrame "Hσ". iSplitR "Hefs".
  - iApply ("IH" with "H HΦ").
  - iApply (big_sepL_impl with "Hefs"); iIntros "!#" (k ef _).
    iIntros "H". iApply ("IH" with "H"); auto.
Qed.

Lemma wp_step s E1 E2 e P Φ :
  to_val e = None →
  (▷ P) -∗ WP e @ s; E2 {{ v, P -∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre. iIntros (->) "HR H".
  iIntros (σ1 κ κs n) "Hσ". iDestruct ("H" with "[$]") as "[$ H]".
  iIntros (e2 σ2 efs Hstep). iDestruct ("H" $! e2 σ2 efs with "[% //]") as "H".
  iIntros "!>". iDestruct "H" as "(Hσ & H & Hefs)".
  iFrame "Hσ Hefs".
  iApply (wp_strong_mono s s E2 with "H"); [done..|].
  iIntros (v) "H". by iApply "H".
Qed.

Lemma wp_bind K `{!LanguageCtx K} s E e Φ :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by apply of_to_val in He as <-. }
  rewrite wp_unfold /wp_pre fill_not_val //.
  iIntros (σ1 κ κs n) "Hσ". iDestruct ("H" with "[$]") as "[% H]".
  iSplit.
  { iPureIntro. destruct s; last done.
    unfold reducible in *. naive_solver eauto using fill_step. }
  iIntros (e2 σ2 efs Hstep).
  destruct (fill_step_inv e σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
  iDestruct ("H" $! e2' σ2 efs with "[//]") as "H". iIntros "!>".
  iDestruct "H" as "(Hσ & H & Hefs)".
  iFrame "Hσ Hefs". by iApply "IH".
Qed.

Lemma wp_bind_inv K `{!LanguageCtx K} s E e Φ :
  WP K e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by rewrite !wp_unfold /wp_pre. }
  rewrite fill_not_val //.
  iIntros (σ1 κ κs n) "Hσ". iDestruct ("H" with "[$]") as "[% H]". iSplit.
  { destruct s; eauto using reducible_fill. }
  iIntros (e2 σ2 efs Hstep).
  iDestruct ("H" $! (K e2) σ2 efs with "[]") as "H"; [by eauto using fill_step|].
  iIntros "!>". iDestruct "H" as "(Hσ & H & Hefs)".
  iFrame "Hσ Hefs". by iApply "IH".
Qed.

(** * Derived rules *)
Lemma wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma wp_stuck_mono s1 s2 E e Φ :
  s1 ⊑ s2 → WP e @ s1; E {{ Φ }} ⊢ WP e @ s2; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed.
Lemma wp_stuck_weaken s E e Φ :
  WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}.
Proof. apply wp_stuck_mono. by destruct s. Qed.
Lemma wp_mask_mono s E1 E2 e Φ : WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros "H"; iApply (wp_strong_mono with "H"); auto. Qed.
Global Instance wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. by apply wp_value'. Qed.
Lemma wp_value_fupd' s E Φ v : Φ v ⊢ WP of_val v @ s; E {{ Φ }}.
Proof. intros. by rewrite -wp_value'. Qed.
Lemma wp_value_fupd s E Φ e v `{!IntoVal e v} :
  (Φ v) ⊢ WP e @ s; E {{ Φ }}.
Proof. intros. rewrite -wp_value //. Qed.
Lemma wp_value_inv s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ⊢ Φ v.
Proof. intros <-. by apply wp_value_inv'. Qed.

Lemma wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

Lemma wp_frame_step_l s E1 E2 e Φ R :
  to_val e = None →
  (▷R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (?) "[Hu Hwp]". iApply (wp_step with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r s E1 E2 e Φ R :
  to_val e = None →
  WP e @ s; E2 {{ Φ }} ∗ (▷R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' s E e Φ R :
  to_val e = None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' s E e Φ R :
  to_val e = None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r s E E); try iFrame; eauto. Qed.

Lemma wp_wand s E e Φ Ψ :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
Qed.
Lemma wp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Ψ :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
End wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{irisG Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Global Instance frame_wp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance elim_acc_wp {X} E1 E2 α β γ e s Φ :
    Atomic (stuckness_to_atomicity s) e →
    ElimAcc (X:=X) (λ x, x) (λ x, x)%I
            α β γ (WP e @ s; E1 {{ Φ }})
            (λ x, WP e @ s; E2 {{ v, β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    intros ?. rewrite /ElimAcc.
    iIntros "Hinner Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "[Hinner Hα]").
    { by iApply wp_mask_mono; iApply ("Hinner" with "[Hα]"). }
    iIntros (v) "[Hβ HΦ]".
    iDestruct ("Hclose" with "Hβ") as "Hclose".
    by iApply "HΦ".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) (λ x, x) (λ x, x)%I
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    rewrite /ElimAcc.
    iIntros "Hinner Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "[Hinner Hα]"); first by iApply "Hinner".
    iIntros (v) "[Hβ HΦ]". iDestruct ("Hclose" with "Hβ") as "Hclose".
    iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.
