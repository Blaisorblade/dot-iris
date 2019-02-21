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
  Context {vls vl: ofeT}.
  Context `{!savedInterpG Σ vls vl}.
  (* Context `{!savedAnythingG Σ (vls -c> vl -c> ▶ ∙)}. *)

  Definition saved_interp_own (γ : gname) (Φ : vls → vl → iProp Σ) :=
    saved_anything_own
      (F := vls -c> vl -c> ▶ ∙) γ (λ vs v, CofeMor Next (Φ vs v)).

  Instance saved_interp_own_contractive γ :
    Contractive (saved_interp_own γ : (vls -c> vl -c> iProp Σ) → iProp Σ).
  Proof.
    intros n X Y HXY.
    rewrite /saved_interp_own /saved_anything_own /=.
    f_equiv. apply to_agree_ne; f_equiv.
    intros x y.
    apply Next_contractive.
    destruct n; simpl in *; auto.
    apply HXY.
  Qed.

  Lemma saved_interp_alloc_strong (G : gset gname) (Φ : vls → vl → iProp Σ) :
    (|==> ∃ γ, ⌜γ ∉ G⌝ ∧ saved_interp_own γ Φ)%I.
  Proof. iApply saved_anything_alloc_strong. Qed.

  Lemma saved_interp_alloc (Φ : vls → vl → iProp Σ) :
    (|==> ∃ γ, saved_interp_own γ Φ)%I.
  Proof. iApply saved_anything_alloc. Qed.

  Lemma saved_interp_agree γ Φ Ψ vs v :
    saved_interp_own γ Φ -∗ saved_interp_own γ Ψ -∗ ▷ (Φ vs v ≡ Ψ vs v).
  Proof.
    unfold saved_pred_own. iIntros "#HΦ #HΨ /=". iApply bi.later_equivI.
    iDestruct (saved_anything_agree with "HΦ HΨ") as "Heq".
    rewrite bi.ofe_fun_equivI; iSpecialize ("Heq" $! vs).
    by rewrite bi.ofe_fun_equivI; iSpecialize ("Heq" $! v); simpl.
  Qed.

  Lemma saved_interp_impl γ Φ Ψ vs v :
    saved_interp_own γ Φ -∗ saved_interp_own γ Ψ -∗ □ (▷ Φ vs v -∗ ▷ Ψ vs v).
  Proof.
    unfold saved_pred_own. iIntros "#HΦ #HΨ /= !# H1".
    iDestruct (saved_anything_agree with "HΦ HΨ") as "Heq".
    rewrite bi.ofe_fun_equivI; iSpecialize ("Heq" $! vs).
    rewrite bi.ofe_fun_equivI; iSpecialize ("Heq" $! v); simpl.
    rewrite bi.later_equivI.
    by iNext; iRewrite -"Heq".
  Qed.

  Lemma saved_interp_agree_eta γ (Φ Ψ : vls -n> vl -n> iProp Σ) vs v :
    saved_interp_own γ (λ (vs : vls) (v : vl), Φ vs v) -∗
    saved_interp_own γ (λ (vs : vls) (v : vl), Ψ vs v) -∗
    ▷ (Φ vs v ≡ Ψ vs v).
  Proof.
    (* Paolo: This manual eta-expansion is needed to get coercions to apply. *)
    iIntros; by iApply (saved_interp_agree _ (λ a, Φ a) (λ a, Ψ a)).
  Qed.
End saved_interp.

Notation "γ ⤇ φ" := (saved_interp_own γ φ) (at level 20).
