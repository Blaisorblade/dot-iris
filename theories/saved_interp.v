From iris.algebra Require Import ofe agree.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.iprop (* For gname *)
     lib.saved_prop.
From iris.program_logic Require Import weakestpre.

From D Require Import tactics.

(** saved interpretations *)

Notation savedInterpG Σ A B := (savedAnythingG Σ (A -c> B -c> ▶ ∙)).
Notation savedInterpΣ A B := (savedAnythingΣ (A -c> B -c> ▶ ∙)).
Section saved_interp.
  Context {vls vl: Type}.
  Context `{!savedInterpG Σ vls vl}.
  Implicit Type (Φ : vls -c> vl -c> iProp Σ).

  Definition saved_interp_own (γ : gname) Φ :=
    saved_anything_own
      (F := vls -c> vl -c> ▶ ∙) γ (λ vs v, Next (Φ vs v)).

  Instance saved_interp_own_contractive γ : Contractive (saved_interp_own γ).
  Proof.
    rewrite /saved_interp_own /saved_anything_own => /= n X Y HXY.
    (do 3 f_equiv) => ??. f_contractive. exact: HXY.
  Qed.

  Lemma saved_interp_alloc_strong (G : gset gname) Φ :
    (|==> ∃ γ, ⌜γ ∉ G⌝ ∧ saved_interp_own γ Φ)%I.
  Proof.
    (* TODO: DROP after the update. *)
    iApply saved_anything_alloc_cofinite || iApply saved_anything_alloc_strong.
  Qed.

  Lemma saved_interp_alloc Φ :
    (|==> ∃ γ, saved_interp_own γ Φ)%I.
  Proof. iApply saved_anything_alloc. Qed.

  Lemma saved_interp_agree γ Φ Ψ vs v :
    saved_interp_own γ Φ -∗ saved_interp_own γ Ψ -∗ ▷ (Φ vs v ≡ Ψ vs v).
  Proof.
    iIntros "#HΦ #HΨ /=". iApply bi.later_equivI.
    iDestruct (saved_anything_agree with "HΦ HΨ") as "Heq".
    rewrite bi.ofe_fun_equivI; iSpecialize ("Heq" $! vs).
    by rewrite bi.ofe_fun_equivI; iSpecialize ("Heq" $! v).
  Qed.

  Lemma saved_interp_impl γ Φ Ψ vs v :
    saved_interp_own γ Φ -∗ saved_interp_own γ Ψ -∗ □ (▷ Φ vs v -∗ ▷ Ψ vs v).
  Proof.
    iIntros "#HΦ #HΨ /= !# H1".
    iPoseProof (saved_interp_agree _ _ _ vs v with "HΦ HΨ") as "Heq".
    by iNext; iRewrite -"Heq".
  Qed.
End saved_interp.

Notation "γ ⤇ φ" := (saved_interp_own γ φ) (at level 20).
