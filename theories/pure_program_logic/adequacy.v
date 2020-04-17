From stdpp Require Import relations.
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Export weakestpre.
Set Default Proof Using "Type".
Import uPred.
Import relations.

(* Program logic adequacy *)
Record adequate `{LangDet Λ} (e1 : expr Λ) (φ : val Λ → Prop) := {
  adequate_result v2 :
    rtc pure_step e1 (of_val v2) → φ v2;
  adequate_not_stuck e2 :
    rtc pure_step e1 e2 → not_stuck e2
}.

(* Theorem adequate_tp_safe {Λ} (e1 e2 : expr Λ) σ  φ :
  adequate e1 σ φ →
  rtc erased_step ([e1], σ) ([e2], σ) →
  is_Some (to_val e2) ∨ ∃ e3, step ([e2], σ) [] ([e3], σ).
Proof.
  intros Had ?.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (adequate_not_stuck NotStuck e1 σ1 φ Had t2 σ2 e2) as [?|(κ&e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists κ, (t2' ++ e3 :: t2'' ++ efs), σ3; econstructor; eauto.
Qed. *)

Section adequacy.
Context `{Hiris : irisG Λ Σ}.

Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Local Notation σ := dummyState.

Lemma wp_step e1 e2 Φ :
  (* to_val e1 = None → *)
  pure_step e1 e2 →
  WP e1 {{ Φ }} -∗ ▷ WP e2 {{ Φ }}.
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (Hpure) "H".
  rewrite (val_stuck e1 σ [] e2 σ []); last exact: pure_to_prim.
  iDestruct "H" as (e2' Hstep') "H".
  suff ->: e2' = e2 by [].
  edestruct Hpure as [_ []]; [done|naive_solver].
Qed.

(* Lemma wptp_step s e1 e2 Φ :
  step ([e1],σ) [] ([e2], σ) →
  WP e1 @ s; ⊤ {{ Φ }} -∗ ▷ WP e2 @ s; ⊤ {{ Φ }}.
Proof.
  iIntros (Hstep) "He".
  destruct Hstep as [e1' σ1' e2' σ2' efs [|? t1'] t2' ?? Hstep];
    simplify_list_eq; last done.
  iDestruct (wp_step with "He") as "H".
Qed. *)

Lemma wptp_steps {n e1 e2 Φ} :
  nsteps pure_step n e1 e2 →
  WP e1 {{ Φ }}
  -∗ ▷^n WP e2 {{ Φ }}.
Proof.
  elim: n e1 => [|n IH] e1 /=; inversion_clear 1; first iIntros "$".
  iIntros "He". by iApply IH; last iApply (wp_step with "He").
Qed.

Lemma wptp_result e1 v2 φ n :
  nsteps pure_step n e1 (of_val v2) →
  WP e1 {{ v, ⌜φ v⌝ }} -∗
  ▷^n ⌜φ v2⌝.
Proof. iIntros (Hs) "He /=". by rewrite (wptp_steps Hs) wp_value_inv'. Qed.

(* Lemma wptp_all_result φ κs' s n e1 t1 κs v2 vs2 σ1 σ2 :
  nsteps n (e1 :: t1, σ1) κs (of_val <$> v2 :: vs2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  WP e1 @ s; ⊤ {{ v,
    state_interp σ2 κs' (length vs2) -∗
    ([∗ list] v ∈ vs2, fork_post v) -∗ ⌜φ v ⌝ }} -∗
  wptp s t1
  -∗ ▷^(S n) ⌜φ v2 ⌝.
Proof.
  iIntros (Hstep) "Hσ He Ht". rewrite laterN_later.
  iDestruct (wptp_steps with "Hσ He Ht") as "H"; first done.
  iNext.
  iDestruct "H" as (e2 t2' ?) "(Hσ & H & Hvs)"; simplify_eq/=.
  rewrite fmap_length. iDestruct (wp_value_inv' with "H") as "H".
  iAssert ([∗ list] v ∈ vs2, fork_post v)%I with "[> Hvs]" as "Hm".
  { clear Hstep. iInduction vs2 as [|v vs] "IH"; csimpl; first by iFrame.
    iDestruct "Hvs" as "[Hv Hvs]".
    iDestruct (wp_value_inv' with "Hv") as "$". by iApply "IH". }
  iNext. iApply ("H" with "Hσ Hm").
Qed. *)

Lemma wp_safe e Φ :
  WP e {{ Φ }} -∗ ⌜not_stuck e⌝.
Proof.
  rewrite wp_unfold /wp_pre /L.not_stuck. iIntros "H".
  destruct (to_val e); first by eauto.
  iDestruct "H" as (e2 ?) "_". iIntros "!%".
  rewrite /reducible; naive_solver.
Qed.

Lemma wptp_safe n e1 e2 Φ :
  nsteps pure_step n e1 e2 →
  WP e1 {{ Φ }} -∗ ▷^n ⌜not_stuck e2⌝.
Proof.
  iIntros (He2) "He".
  iDestruct (wptp_steps with "He") as "H"; first done.
  iNext.
  iApply (wp_safe with "H").
Qed.
End adequacy.

Theorem wp_adequacy {Σ Λ} e φ `{LangDet Λ} :
  (⊢@{iPropI Σ} let _ := IrisG Λ Σ in |==> WP e {{ v, ⌜φ v⌝ }}) →
  adequate e (λ v, φ v).
Proof.
  intros Hwp; split; intros ? [n Hsteps]%rtc_nsteps; eapply (soundness _ n);
    iMod Hwp as "Hwp".
  by iApply (wptp_result e with "Hwp").
  by iApply (wptp_safe with "Hwp").
Qed.
