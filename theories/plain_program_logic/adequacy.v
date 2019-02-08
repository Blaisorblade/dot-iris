From stdpp Require Import namespaces.
From D.plain_program_logic Require Export weakestpre.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

(* Program logic adequacy *)
Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ)
    (φ : val Λ → state Λ → Prop) := {
  adequate_result t2 σ2 v2 :
   rtc erased_step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
  adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   rtc erased_step ([e1], σ1) (t2, σ2) →
   e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2)
}.

Theorem adequate_tp_safe {Λ} (e1 : expr Λ) t2 σ1 σ2 φ :
  adequate NotStuck e1 σ1 φ →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ κ t3 σ3, step (t2, σ2) κ (t3, σ3).
Proof.
  intros Had ?.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (adequate_not_stuck NotStuck e1 σ1 φ Had t2 σ2 e2) as [?|(κ&e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists κ, (t2' ++ e3 :: t2'' ++ efs), σ3; econstructor; eauto.
Qed.

Section adequacy.
Context `{irisG Λ Σ}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Notation wptp s t := ([∗ list] ef ∈ t, WP ef @ s; ⊤ {{ fork_post }})%I.

Lemma wp_step s e1 σ1 κ κs e2 σ2 efs m Φ :
  prim_step e1 σ1 κ e2 σ2 efs →
  state_interp σ1 (κ ++ κs) m -∗ WP e1 @ s; ⊤ {{ Φ }} -∗ ▷
  (state_interp σ2 κs (length efs + m) ∗ WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s efs).
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (?) "Hσ H".
  rewrite (val_stuck e1 σ1 κ e2 σ2 efs) //.
  iMod ("H" $! σ1 with "Hσ") as "(_ & H)".
  iDestruct ("H" $! e2 σ2 efs with "[//]") as "H".
  by iIntros "!>".
Qed.

Lemma wptp_step s e1 t1 t2 κ κs σ1 σ2 Φ :
  step (e1 :: t1,σ1) κ (t2, σ2) →
  state_interp σ1 (κ ++ κs) (length t1) -∗ WP e1 @ s; ⊤ {{ Φ }} -∗ wptp s t1 -∗
  ∃ e2 t2', ⌜t2 = e2 :: t2'⌝ ∗
    ▷ (state_interp σ2 κs (pred (length t2)) ∗ WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s t2').
Proof.
  iIntros (Hstep) "Hσ He Ht".
  destruct Hstep as [e1' σ1' e2' σ2' efs [|? t1'] t2' ?? Hstep]; simplify_eq/=.
  - iExists e2', (t2' ++ efs). iSplitR; first by eauto.
    iDestruct (wp_step with "Hσ He") as "H"; first done.
    iIntros "!>". iDestruct "H" as "(Hσ & He2 & Hefs)".
    rewrite Nat.add_comm app_length. iFrame.
  - iExists e, (t1' ++ e2' :: t2' ++ efs); iSplitR; first eauto.
    iFrame "He". iDestruct "Ht" as "(Ht1 & He1 & Ht2)".
    iDestruct (wp_step with "Hσ He1") as "H"; first done.
    iIntros "!>". iDestruct "H" as "(Hσ & He2 & Hefs)".
    rewrite !app_length /= !app_length.
    replace (length t1' + S (length t2' + length efs))
      with (length efs + (length t1' + S (length t2'))) by omega. iFrame.
Qed.

Lemma wptp_steps s n e1 t1 κs κs' t2 σ1 σ2 Φ :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗ WP e1 @ s; ⊤ {{ Φ }} -∗ wptp s t1
  -∗ ▷^n ∃ e2 t2',
    ⌜t2 = e2 :: t2'⌝ ∗
    state_interp σ2 κs' (pred (length t2)) ∗
    WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s t2'.
Proof.
  revert e1 t1 κs κs' t2 σ1 σ2; simpl.
  induction n as [|n IH]=> e1 t1 κs κs' t2 σ1 σ2 /=.
  { inversion_clear 1; iIntros "???"; iExists e1, t1; iFrame; eauto 10. }
  iIntros (Hsteps) "Hσ He Ht". inversion_clear Hsteps as [|?? [t1' σ1']].
  rewrite -(assoc_L (++)).
  iDestruct (wptp_step with "Hσ He Ht") as (e1' t1'' ?) "H";
    first eauto; simplify_eq.
  iIntros "!>". iDestruct "H" as "(Hσ & He & Ht)".
  by iApply (IH with "Hσ He Ht").
Qed.

Lemma wptp_result φ κs' s n e1 t1 κs v2 t2 σ1 σ2  :
  nsteps n (e1 :: t1, σ1) κs (of_val v2 :: t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  WP e1 @ s; ⊤ {{ v, ∀ σ, state_interp σ κs' (length t2) -∗ ⌜φ v σ⌝ }} -∗
  wptp s t1 -∗ ▷^(S n) ⌜φ v2 σ2⌝.
Proof.
  iIntros (?) "Hσ He Ht". rewrite laterN_later.
  iDestruct (wptp_steps with "Hσ He Ht") as "H"; first done.
  iNext.
  iDestruct "H" as (? ?) "(%&?&Hwp&_)"; simpl in *; simplify_eq.
  iMod (wp_value_inv' with "Hwp") as "Hwp".
  iNext.
  by iApply "Hwp".
Qed.

Lemma wptp_all_result φ κs' s n e1 t1 κs v2 vs2 σ1 σ2 :
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
  rewrite fmap_length. iMod (wp_value_inv' with "H") as "H".
  iAssert ([∗ list] v ∈ vs2, fork_post v)%I with "[> Hvs]" as "Hm".
  { clear Hstep. iInduction vs2 as [|v vs] "IH"; csimpl; first by iFrame.
    iDestruct "Hvs" as "[Hv Hvs]".
    iMod (wp_value_inv' with "Hv") as "$". by iApply "IH". }
  iNext. iApply ("H" with "Hσ Hm").
Qed.

Lemma wp_safe κs m e σ Φ :
  state_interp σ κs m -∗
  WP e {{ Φ }} -∗ ▷ (⌜is_Some (to_val e) ∨ reducible e σ⌝).
Proof.
  rewrite wp_unfold /wp_pre. iIntros "Hσ H".
  destruct (to_val e) as [v|] eqn:?; first eauto.
  iMod ("H" $! σ [] κs with "Hσ") as "[% H]"; eauto.
Qed.

Lemma wptp_safe κs' n e1 κs e2 t1 t2 σ1 σ2 Φ :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) → e2 ∈ t2 →
  state_interp σ1 (κs ++ κs') (length t1) -∗ WP e1 {{ Φ }} -∗ wptp NotStuck t1
  -∗ ▷^(S n) ⌜is_Some (to_val e2) ∨ reducible e2 σ2⌝.
Proof.
  iIntros (? He2) "Hσ He Ht". rewrite laterN_later.
  iDestruct (wptp_steps  with "Hσ He Ht") as "H"; first done.
  iNext.
  iDestruct "H" as (e2' t2' ?) "(Hσ & H & Ht)"; simplify_eq.
  apply elem_of_cons in He2 as [<-|(t1''&t2''&->)%elem_of_list_split].
  - iMod (wp_safe with "Hσ H") as "$"; auto.
  - iDestruct "Ht" as "(_ & He2 & _)". by iMod (wp_safe with "Hσ He2").
Qed.

End adequacy.

Theorem wp_strong_adequacy Σ Λ s e σ φ :
  (∀ κs,
     (|==> ∃
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ stateI fork_post in
       (* This could be strengthened so that φ also talks about the number
       of forked-off threads *)
       stateI σ κs 0 ∗ WP e @ s; ⊤ {{ v, ∀ σ m, stateI σ [] m -∗ ⌜φ v σ⌝ }})%I) →
  adequate s e σ φ.
Proof.
  intros Hwp; split.
  - intros t2 σ2 v2 [n [κs ?]]%erased_steps_nsteps.
    eapply (soundness _ (S (S n))). rewrite later_laterN.
    iMod (Hwp (κs ++ [])) as (stateI fork_post) "[Hσ Hwp]".
    iNext.
    iApply (@wptp_result _ _ (IrisG _ _ stateI fork_post) with "[Hσ] [Hwp]"); eauto.
    iApply (wp_wand with "Hwp"). iIntros (v) "H"; iIntros (σ'). iApply "H".
  - destruct s; last done. intros t2 σ2 e2 _ [n [κs ?]]%erased_steps_nsteps ?.
    eapply (soundness _ (S (S n))). rewrite later_laterN.
    iMod (Hwp (κs ++ [])) as (stateI fork_post) "[Hσ Hwp]".
    iNext.
    iApply (@wptp_safe _ _ (IrisG _ _ stateI fork_post) with "[Hσ] Hwp"); eauto.
Qed.

Theorem wp_adequacy Σ Λ s e σ φ :
  (∀ κs,
     (|==> ∃ stateI : state Λ → list (observation Λ) → iProp Σ,
       let _ : irisG Λ Σ := IrisG _ _ (λ σ κs _, stateI σ κs) (λ _, True%I) in
       stateI σ κs ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }})%I) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply (wp_strong_adequacy Σ _)=> κs.
  iMod Hwp as (stateI) "[Hσ H]". iExists (λ σ κs _, stateI σ κs), (λ _, True%I).
  iIntros "{$Hσ} !>".
  iApply (wp_wand with "H"). iIntros (v ? σ') "_".
  iIntros "_"; auto.
Qed.

Theorem wp_strong_all_adequacy Σ Λ `{invPreG Σ} s e σ1 v vs σ2 φ :
  (∀ κs,
     (|==> ∃
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ stateI fork_post in
       stateI σ1 κs 0 ∗ WP e @ s; ⊤ {{ v,
         stateI σ2 [] (length vs) -∗
         ([∗ list] v ∈ vs, fork_post v) -∗ ⌜ φ v ⌝ }})%I) →
  rtc erased_step ([e], σ1) (of_val <$> v :: vs, σ2) →
  φ v.
Proof.
  intros Hwp [n [κs ?]]%erased_steps_nsteps.
  eapply (soundness _ (S (S n))). rewrite later_laterN.
  iMod Hwp as (stateI fork_post) "[Hσ Hwp]".
  iNext.
  iApply (@wptp_all_result _ _ (IrisG _ _ stateI fork_post)
    with "[Hσ] [Hwp]"); eauto. by rewrite right_id_L.
Qed.
