From iris.program_logic Require Import adequacy.
From iris.proofmode Require Import tactics.
From D Require Import tactics.
From D.Dot Require Import unary_lr.

Theorem adequacy Σ `{HdotG: dotPreG Σ} e e' thp σ σ' T ρ:
  (forall `{dotG Σ}, True ⊢ ⟦ T ⟧ₑ ρ e) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hlog ??. cut (adequate NotStuck e σ (λ _ _, True)); first (intros [_ ?]; eauto).
  eapply (wp_adequacy Σ); eauto. apply HdotG.
  iIntros (Hinv ?). iModIntro. iExists (λ _ _, True%I). iSplit=> //.
  (* rewrite -(empty_env_subst e). *)
  set (DotΣ := DotG Σ Hinv _).
  iApply (wp_wand with "[]"); by [iApply Hlog | auto].
Qed.

(* Instead of still assuming semantic typing, here we should assume syntactic
   typing and use the fundamental lemma. But otherwise this follows the general
   instantiation pattern, from e.g.
   https://gitlab.mpi-sws.org/iris/examples/blob/a89dc12821b63eeb9b831d21629ac55ebd601f38/theories/logrel/F_mu_ref/soundness.v#L29-39. *)
Corollary almost_type_soundness e e' thp σ σ' T:
  (forall `{dotG Σ}, True ⊢ ⟦ T ⟧ₑ [] e) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros ??. set (Σ := dotΣ).
  (* set (HG := DotPreG Σ _ (subG_savedAnythingΣ _)). *)
  set (HG := _: dotPreG Σ).
  eapply (adequacy Σ).
  - intros ?.
    apply H.
      (* by apply fundamental. *)
  - eauto.
Qed.
