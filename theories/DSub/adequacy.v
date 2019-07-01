From iris.proofmode Require Import tactics.
From D Require Import swap_later_impl.
From D.DSub Require Import unary_lr.

Import dlang_adequacy.

Theorem adequacy Σ `{HdlangG: dlangPreG Σ} `{!SwapProp (iPropSI Σ)} e e' thp σ σ' T ρ:
  (forall `{dlangG Σ} `{SwapProp (iPropSI Σ)}, True ⊢ ⟦ T ⟧ₑ ρ e) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hlog.
  eapply (adequacy _) => Hdlang Hswap.
  iDestruct (Hlog with "[#]") as "H"; iIntros; by [].
Qed.

(* Instead of still assuming semantic typing, here we should assume syntactic
   typing and use the fundamental lemma. But otherwise this follows the general
   instantiation pattern, from e.g.
   https://gitlab.mpi-sws.org/iris/examples/blob/a89dc12821b63eeb9b831d21629ac55ebd601f38/theories/logrel/F_mu_ref/soundness.v#L29-39. *)
Corollary almost_type_soundness e e' thp σ σ' T:
  (forall `{dlangG Σ} `{SwapProp (iPropSI Σ)}, True ⊢ ⟦ T ⟧ₑ [] e) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros; eapply (adequacy dlangΣ) => //.
  exact: H.
  (* by apply fundamental. *)
Qed.
