From iris.proofmode Require Import tactics.
From D Require Import tactics proofmode_extra.
From iris.base_logic Require Import base_logic.
From D.Dot Require Import operational synLemmas.
Import uPred.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (p : path)
         (Γ : ctx) (ρ : vls).

(*
Fixpoint path_fill (ls : list label) p : path :=
  match ls with
  | [] => p
  | l :: ls => pself (path_fill ls p) l
  end.

Fixpoint path_split p : list label * vl :=
  match p with
  | pv v => ([], v)
  | pself p l => let '(ls, v) := path_split p in (l :: ls, v)
  end.

Lemma path_inv p : let '(ls, v) := path_split p in
  path_fill ls (pv v) = p.
Proof.
  elim: p => [v // | p IHp l /=].
  case: (path_split p) IHp => /= ?? -> //.
Qed. *)
(* Lemma path_inv_2 ls v : path_split (path_fill ls (pv v)) = (ls, v).
Proof. elim: ls => [// | l ls /= -> //]. Qed. *)

(* Section lemmas.
  Context `{HdlangG: dlangG Σ}.
  Implicit Types (φ : vl → iProp Σ).
  Definition path_wp_bind_0 p φ :
    path_wp p φ = path_wp p (λ v, path_wp (pv v) φ) := eq_refl.

  Lemma path_wp_bind ls p φ:
    path_wp (path_fill ls p) φ = path_wp p (λ w, path_wp (path_fill ls (pv w)) φ).
  Proof.
    elim: ls φ => [// | l ls /= IHls ?].
    exact: IHls.
  Qed.
End lemmas. *)

Section path_wp.
  Context `{HdlangG: dlangG Σ}.
  Implicit Types (φ : vl → iProp Σ).

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
    | pself p l => path_wp p (λ vp, ∃ vq, ⌜ vp @ l ↘ dvl vq ⌝ ∧ ▷ φ vq)
    | pv vp => φ vp
    end%I.

  Global Instance path_wp_persistent φ p:
    (∀ v, Persistent (φ v)) → Persistent (path_wp p φ).
  Proof. elim: p φ => *; apply _. Qed.

  Lemma strong_path_wp_wand φ1 φ2 p:
    path_wp p φ1 -∗
    ▷^(plength p) (∀ v, φ1 v -∗ φ2 v) -∗
    path_wp p φ2.
  Proof.
    elim: p φ1 φ2 => /= [v|p IHp l] ??; iIntros "H1 Hwand";
      first by iApply "Hwand".
    iApply (IHp with "H1").
    iNext.
    iIntros (v) "H"; iDestruct "H" as (vq Hl) "?".
    iExists vq; iFrame (Hl). by iApply "Hwand".
  Qed.

  Lemma path_wp_wand φ1 φ2 p:
    path_wp p φ1 -∗
    (∀ v, φ1 v -∗ φ2 v) -∗
    path_wp p φ2.
  Proof.
    iIntros "Hp1 Hwand".
    iApply (strong_path_wp_wand with "Hp1"); by iNext.
  Qed.

  Lemma path_wp_eq p φ :
    path_wp p φ ⊣⊢ ∃ v, path_wp p (λ w, ⌜ w = v ⌝) ∧ ▷^(plength p) φ v.
  Proof.
    elim: p φ => [ v | p IHp l ] φ /=; iSplit; iIntros "H".
    - auto.
    - by iDestruct "H" as (w <-) "H".
    - rewrite IHp.
      iDestruct "H" as (v) "[Hp Hw]".
      iDestruct "Hw" as (w) "[Hl Hw]".
      iExists w; iSplit; last by iNext.
      iApply (strong_path_wp_wand with "Hp").
      iIntros (? ->); iExists w. by iSplit.
    - setoid_rewrite IHp.
      iDestruct "H" as (w) "[Hp Hw]".
      iDestruct "Hp" as (v) "[Hp Hl]".
      iExists v; iSplit; first done.
      iDestruct "Hl" as (w') "[Hl Heqw]".
      iExists w'; iSplit; first done.
      iNext; iNext; by iDestruct "Heqw" as %->.
  Qed.

  Lemma path_wp_det p v1 v2:
    path_wp p (λ w, ⌜ w = v1 ⌝) -∗
    path_wp p (λ w, ⌜ w = v2 ⌝) -∗
    ▷^(plength p) ⌜ v1 = v2 ⌝: iProp Σ.
  Proof.
    elim: p v1 v2 => [v /=| p /= IHp l //] v1 v2;
      first by iIntros (<- <-).
    rewrite !path_wp_eq.
    iIntros "H1 H2".
    iDestruct "H1" as (w1) "[H1 Hl1]".
    iDestruct "H2" as (w2) "[H2 Hl2]".
    iDestruct (IHp with "H1 H2") as "Heq".
    rewrite -swap_later; iNext (plength p).
    iDestruct "Heq" as %<-.
    iDestruct "Hl1" as (vq1 Hl1) "Heq1".
    iDestruct "Hl2" as (vq2 Hl2) "Heq2".
    iNext. objLookupDet. iDestruct "Heq1" as %->. by [].
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

  Lemma path_wp_cl n p v:
    path_wp p (λ w, ⌜ w = v ⌝) -∗
    ▷^(plength p) ⌜ nclosed p n → nclosed_vl v n ⌝.
  Proof.
    elim: p v => /= [w|p IHp l] v.
    - iPureIntro. move => ->. exact: fv_pv_inv.
    - rewrite path_wp_eq -swap_later.
      iIntros "H". iDestruct "H" as (w) "[Hpwp H]".
      rewrite IHp.
      iNext (plength p).
      iDestruct "Hpwp" as %Himpl.
      iDestruct "H" as (v' Hl) "> ->". iPureIntro => Hclps.
      enough (nclosed (dvl v) n). by eauto with fv.
      eapply nclosed_lookup', Himpl; eauto with fv.
  Qed.

(*
  Instance v l w: Timeless (⌜ v @ l ↘ w ⌝: iProp Σ)%I := _.
  Instance Timeless_path_wp p φ {Hφ: ∀ v, Timeless (φ v)}:
    Timeless (path_wp p φ).
  Proof.
    (* move: Hφ. rewrite /Timeless => Hφ. *)
    elim: p φ Hφ => /= [v //|p IHp l] φ Hφ.
    (* exact (Hφ v 0). *)
    apply IHp.
    rewrite /Timeless.
    iIntros (v) "H".
    iDestruct "H" as (vq) "[>% H]".
    iExists vq. iSplit => //. iApply timeless => //.
    move: (Hφ vq) => {Hφ} Hφ.

    Import uPred.
    rewrite /Timeless /sbi_except_0 -later_or.
    iIntros "H".
    Check (strip_timeless_laterN_wand 1 (▷(φ vq)) ((False ∨ φ vq)))%I. => /=. auto.
    auto.
    iIntros.  iRight. done.
    move: Hφ.
     => Hφ.
    (* rewrite /Timeless in Hφ. *)
    iNext. iDestruct (Hφ with "H") as "[H | H]"; last by iRight.
    iLeft.
    rewrite timeless /sbi_except_0. iDestruct "H" as "[H|H]".
    iDestruct (timeless_timelessN 2 with "H") as "[H|H]".
    iLeft. iNext.
    apply _.
    iDe
    iEval (rewrite path_wp_wand). *)

End path_wp.
