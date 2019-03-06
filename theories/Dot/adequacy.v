From D.pure_program_logic Require Import adequacy.
From iris.proofmode Require Import tactics.
From D Require Import tactics.
From D.Dot Require Import unary_lr typeExtractionSem fundamental typing.

Theorem adequacy Σ `{HdotG: dotPreG Σ} e e' thp σ σ' T:
  (forall `{dotG Σ}, allGs ∅ ⊢ |==> [] ⊨ e : T) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hlog ??. cut (adequate NotStuck e σ (λ _ _, True)); first (intros [_ ?]; eauto).
  eapply (wp_adequacy Σ) => /=.
  iMod (gen_iheap_init (hG := dotPreG_interpNames) ∅) as (g) "Hgs".
  set (DotΣ := DotG Σ _ g).
  iMod (Hlog DotΣ with "Hgs") as "[_ #Hlog]".
  iIntros (?) "!>". iExists (λ _ _, True%I); iSplit=> //.
  iEval (replace e with (e.|[to_subst []]) by by asimpl).
  iApply wp_wand; by [iApply "Hlog" | auto].
Qed.

(* Instead of still assuming semantic typing, here we should assume syntactic
   typing and use the fundamental lemma. But otherwise this follows the general
   instantiation pattern, from e.g.
   https://gitlab.mpi-sws.org/iris/examples/blob/a89dc12821b63eeb9b831d21629ac55ebd601f38/theories/logrel/F_mu_ref/soundness.v#L29-39. *)
Corollary type_soundness e e' thp σ σ' T `{stampTable}:
  ([] ⊢ₜ e : T) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros ??. set (Σ := dotΣ).
  eapply (adequacy Σ).
  - iIntros; by iApply fundamental_typed_upd.
  - eauto.
Qed.
