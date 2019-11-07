From iris.proofmode Require Import tactics.
From D Require Import iris_prelude.
From D.Dot Require Import dlang_inst.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (p : path)
         (Γ : ctx) (ρ : vls).

Lemma plength_subst_inv p s :
  plength p.|[s] = plength p.
Proof. by elim: p => [v| p /= ->]. Qed.

Section path_wp.
  Context `{HdlangG: dlangG Σ}.
  Implicit Types (φ : vl -d> iPropO Σ).

  (** A simplified variant of weakest preconditions for path evaluation.
      The difference is that path evaluation is completely pure, and
      postconditions must hold now, not after updating resources.
      vp ("Value from Path") and vq range over results of evaluating paths.

      Path evaluation was initially more complex; now that we got to this
      version, I wonder whether we can just use the standard Iris WP, but I am
      not sure if that would work.
      *)
  Fixpoint path_wp p φ: iProp Σ :=
    match p with
    | pself p l => path_wp p (λ v, ∃ w, ⌜ v @ l ↘ dvl w ⌝ ∧ φ w)
    | pv vp => φ vp
    end%I.

  Global Instance path_wp_ne p : NonExpansive (path_wp p).
  Proof.
    elim: p => [w|p IHp l] n x y Heq /=. done.
    f_equiv => vp. f_equiv => vq. f_equiv. exact: Heq.
  Qed.

  Global Instance path_wp_persistent φ p:
    (∀ v, Persistent (φ v)) → Persistent (path_wp p φ).
  Proof. elim: p φ => *; apply _. Qed.

  Global Instance Proper_pwp: Proper ((=) ==> pointwise_relation _ (≡) ==> (≡)) path_wp.
  Proof.
    (* The induction works best in this shape, but this instance is best kept local. *)
    have Proper_pwp_2: ∀ p, Proper (pointwise_relation _ (≡) ==> (≡)) (path_wp p).
    elim; solve_proper.
    solve_proper.
  Qed.

  Lemma path_wp_wand φ1 φ2 p:
    path_wp p φ1 -∗
    (∀ v, φ1 v -∗ φ2 v) -∗
    path_wp p φ2.
  Proof.
    elim: p φ1 φ2 => /= [v|p IHp l] ??; iIntros "H1 Hwand";
      first by iApply "Hwand".
    iApply (IHp with "H1").
    iIntros (v); iDestruct 1 as (vq Hl) "?".
    iExists vq; iFrame (Hl). by iApply "Hwand".
  Qed.

  Lemma path_wp_eq p φ :
    path_wp p φ ⊣⊢ ∃ v, path_wp p (λ w, ⌜ w = v ⌝) ∧ φ v.
  Proof.
    elim: p φ => [ v | p IHp l ] φ /=; iSplit; iIntros "H".
    - auto.
    - by iDestruct "H" as (w <-) "H".
    - rewrite IHp.
      iDestruct "H" as (v) "[Hp Hw]".
      iDestruct "Hw" as (w) "[Hl Hw]".
      iExists w; iSplit; last by [].
      iApply (path_wp_wand with "Hp").
      iIntros (? ->); iExists w. by iSplit.
    - setoid_rewrite IHp.
      iDestruct "H" as (w) "[Hp Hw]".
      iDestruct "Hp" as (v) "[Hp Hl]".
      iExists v; iSplit; first done.
      iDestruct "Hl" as %(w' & Hl & ->). auto.
  Qed.

  Lemma path_wp_det p v1 v2:
    path_wp p (λ w, ⌜ w = v1 ⌝) -∗
    path_wp p (λ w, ⌜ w = v2 ⌝) -∗
    ⌜ v1 = v2 ⌝: iProp Σ.
  Proof.
    elim: p v1 v2 => [v /=| p /= IHp l //] v1 v2;
      first by iIntros (<- <-).
    rewrite !path_wp_eq.
    iDestruct 1 as (w1) "[H1 Hl1]".
    iDestruct 1 as (w2) "[H2 Hl2]".
    iDestruct (IHp with "H1 H2") as %<-.
    iDestruct "Hl1" as %(vq1 & Hl1 & ->).
    iDestruct "Hl2" as %(vq2 & Hl2 & ->).
    objLookupDet. by [].
  Qed.

  Lemma path_wp_later_swap p φ:
    path_wp p (λ v, ▷ φ v) ⊢ ▷ path_wp p (λ v, φ v).
  Proof.
    elim: p φ => [v // | p IHp l /=] φ.
    rewrite -IHp.
    iIntros "H".
    iApply (path_wp_wand with "H").
    iIntros (v) "H".
    iDestruct "H" as (w) "H"; iExists w.
    iDestruct "H" as "[$ $]".
  Qed.

  Lemma path_wp_laterN_swap p φ i:
    path_wp p (λ v, ▷^i φ v) ⊢ ▷^i path_wp p (λ v, φ v).
  Proof.
    elim: i => [// | i /= <-].
    rewrite path_wp_later_swap. by [].
  Qed.

  Global Instance Plain_path_wp p φ (H : (∀ v, Plain (φ v))) :
    Plain (path_wp p φ).
  Proof.
    elim: p φ H => /= [//|p IHp l] φ H; rewrite path_wp_eq /Plain.
    iDestruct 1 as (v) "#[Heq H]"; iDestruct "H" as (w Hl) "#H".
    iModIntro. repeat (iExists _; iSplit => //).
  Qed.
End path_wp.
