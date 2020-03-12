From iris.proofmode Require Import tactics.
From D Require Import swap_later_impl.
From D.DSub Require Import unary_lr rules.

Import dlang_adequacy.

Theorem adequacy_dsub_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} e T:
  (∀ `(dlangG Σ) `(!SwapPropI Σ), [] ⊨ e : T) →
  safe e.
Proof.
  intros Hlog ?*. eapply (safety_dlang _).
  iIntros (??) "Hs". iDestruct Hlog as "#Htyp".
  by iSpecialize ("Htyp" $! ids with "[#//]"); rewrite hsubst_id.
Qed.

(* Instead of still assuming semantic typing, here we should assume syntactic
   typing and use the fundamental lemma. But otherwise this follows the general
   instantiation pattern, from e.g.
   https://gitlab.mpi-sws.org/iris/examples/blob/a89dc12821b63eeb9b831d21629ac55ebd601f38/theories/logrel/F_mu_ref/soundness.v#L29-39. *)
Corollary almost_type_soundness e T:
  (∀ `(dlangG Σ) `(!SwapPropI Σ), [] ⊨ e : T) →
  safe e.
Proof.
  intros; eapply (adequacy_dsub_sem dlangΣ) => //.
  exact: H.
  (* by apply fundamental. *)
Qed.
