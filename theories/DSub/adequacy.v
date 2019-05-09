From D.pure_program_logic Require Import adequacy.
From iris.proofmode Require Import tactics.
From D Require Import tactics swap_later_impl.
From D.DSub Require Import unary_lr.
Require Import Program.

Theorem adequacy Σ `{HdsubG: dsubPreG Σ} `{!SwapProp (iPropSI Σ)} e e' thp σ σ' T ρ:
  (forall `{dsubG Σ} `{SwapProp (iPropSI Σ)}, True ⊢ ⟦ T ⟧ₑ ρ e) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hlog ??. cut (adequate NotStuck e σ (λ _ _, True)); first (intros [_ ?]; eauto).
  eapply (wp_adequacy Σ) => /=.
  iMod (gen_iheap_init (hG := dsubPreG_interpNames) ∅) as (g) "H".
  iIntros (?) "!>". iExists (λ _ _, True%I); iSplit=> //.
  set (DsubΣ := DsubG Σ _ g).
  specialize (@Hlog _ _).
  iApply wp_wand; by [iApply Hlog | auto].
Qed.

Instance CmraSwappable_dsub: CmraSwappable (iResUR dsubΣ).
Proof.
  apply Swappable_iResUR.
  rewrite /gid; repeat (dependent destruction i; cbn; try apply _).
Qed.

(* Instead of still assuming semantic typing, here we should assume syntactic
   typing and use the fundamental lemma. But otherwise this follows the general
   instantiation pattern, from e.g.
   https://gitlab.mpi-sws.org/iris/examples/blob/a89dc12821b63eeb9b831d21629ac55ebd601f38/theories/logrel/F_mu_ref/soundness.v#L29-39. *)
Corollary almost_type_soundness e e' thp σ σ' T:
  (forall `{dsubG Σ} `{SwapProp (iPropSI Σ)}, True ⊢ ⟦ T ⟧ₑ [] e) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros; eapply (adequacy dsubΣ) => //.
  exact: H.
  (* by apply fundamental. *)
Qed.
