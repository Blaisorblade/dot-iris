From iris.proofmode Require Import tactics.
Import bi.

Module Tests1.
  Section Fail.
    Context {PROP : sbi}.
    Implicit Types P Q R : PROP.

    Lemma demo_laterN_forall P Q n: (▷^n ∀ x: string, P) -∗ (▷^n ∀ x: string, Q).
    Proof.
      iIntros "H". Fail iIntros (w).
      Fail iSpecialize ("H" $! "a").
    Abort.
  End Fail.
End Tests1.

Section proofmode_extra.
  Context {PROP : sbi}.
  Implicit Types P Q R : PROP.

  Lemma swap_later {n} P: ▷^n ▷ P ⊣⊢ ▷ ▷^n P.
  Proof. by rewrite -bi.later_laterN bi.laterN_later. Qed.

  Global Instance from_forall_laterN {A} P (Φ : A → PROP) n :
        FromForall P Φ → FromForall (▷^n P)%I (λ a, ▷^n (Φ a))%I.
  Proof. rewrite /FromForall => <-. by rewrite laterN_forall. Qed.

  Global Instance into_forall_laterN {A} P (Φ : A → PROP) n :
    IntoForall P Φ → IntoForall (▷^n P) (λ a, ▷^n (Φ a))%I.
  Proof. rewrite /IntoForall=> HP. by rewrite HP laterN_forall. Qed.
End proofmode_extra.

Module Test_Succeeds.
  Section foo.
    Context {PROP : sbi}.
    Lemma demo_laterN_forall {A} (Φ Ψ: A → PROP) n: (∀ x, ▷^n Φ x) -∗ ▷^n (∀ x, Φ x).
    Proof.
      iIntros "H" (w). iApply ("H" $! w).
    Qed.
  End foo.
End Test_Succeeds.

From iris.base_logic Require Import base_logic lib.iprop.

Import uPred.

Section uPred_later_extra.
  Context `{M: ucmraT}.
  Implicit Types (Q: uPred M) (x: M).

  Lemma laterN_pure_id i n P x: i <= n →
    (▷^i uPred_pure_def P)%I n x → P.
  Proof.
    move => Hle H; induction i => //=.
    apply IHi; first lia.
    elim: i n Hle H {IHi} => [|i IHi] [|n] Hle;
      unseal => // H; first lia.
    apply IHi; first lia. by unseal.
  Qed.

  Lemma laterN_trivial i n Q x: i > n →
    (▷^i Q)%I n x.
  Proof.
    move: i => [|i] Hle. by lia.
    apply uPred_mono with i x; eauto with lia.
    elim: i {Hle}; by unseal.
  Qed.

  Lemma strip_pure_later P Q:
    (⌜ P ⌝ → ▷ Q) ⊢ (▷ ⌜ P ⌝ → ▷ Q).
  Proof.
    unseal; constructor => n x Hvx Hyp [|n'] // ?????.
    by apply Hyp.
  Qed.

  Lemma strip_pure_laterN i P Q:
    (⌜ P ⌝ → ▷^i Q) ⊢ ▷^i ⌜ P ⌝ → ▷^i Q.
  Proof.
    unseal; constructor => n x Hvx Hyp n' //= x' ?? Hvx' H.
    destruct (decide (i <= n')) as [Hle|Hge].
    - by eapply Hyp, laterN_pure_id.
    - by apply laterN_trivial; lia.
  Qed.
End uPred_later_extra.

From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

Section wp_extra.
  Context `{irisG Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Lemma wp_strong_mono_wf s1 s2 E1 E2 e Φ {Ψ} (wf: expr Λ → Prop):
    s1 ⊑ s2 →
    wf e →
    (∀ t1 t2 σ σ' ts κ, prim_step t1 σ κ t2 σ' ts → wf t1 → wf t2 ∧ Forall wf ts) →
    WP e @ s1; E1 {{ Φ }} -∗
    (∀ v, ⌜wf (of_val v)⌝ -∗ Φ v -∗ Ψ v) -∗
    WP e @ s2; E2 {{ Ψ }}.
  Proof.
    iIntros (? HwfE Hpres) "H HΦ". iLöb as "IH" forall (e HwfE E1 E2 Φ Ψ).
    rewrite !wp_unfold /wp_pre.
    destruct (to_val e) as [v|] eqn:?.
    { iApply ("HΦ" with "[%] [-//]"). apply of_to_val in Heqo. by subst. }
    iIntros (σ1 κ κs n) "Hσ".
    iDestruct ("H" with "[$]") as "[% H]".
    iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 efs Hstep).
    iDestruct ("H" with "[//]") as "H". iIntros "!>".
    have HPefs: Forall wf efs. by eapply Hpres.
    iDestruct "H" as "(Hσ & H & Hefs)".
    iFrame "Hσ". iSplitR "Hefs".
    - iApply ("IH" with "[%] H HΦ"). by eapply Hpres.
    - iApply (big_sepL_impl with "Hefs"); iIntros "!#" (k ef Heq).
      iIntros "H". iApply ("IH" with "[%] H"); auto.
      edestruct (Hpres e e2) => //. by eapply Forall_lookup_1.
  Qed.

  Lemma wp_wand_wf s E e Φ {Ψ} (wf: expr Λ → Prop):
    wf e →
    (∀ t1 t2 σ σ' ts κ, prim_step t1 σ κ t2 σ' ts → wf t1 → wf t2 ∧ Forall wf ts) →
    WP e @ s; E {{ v, Φ v }} -∗
    (∀ v, ⌜wf (of_val v)⌝ -∗ Φ v -∗ Ψ v) -∗
    WP e @ s; E {{ v, Ψ v }}.
  Proof.
    iIntros (HwfE Hpres) "Hwp HΦ". iApply (wp_strong_mono_wf with "Hwp"); eauto.
  Qed.

  Lemma wp_and `{∀ σ κ n, Persistent (state_interp σ κ n)} (P1 P2: val Λ → iProp Σ) e:
    WP e {{ P1 }} -∗ WP e {{ P2 }} -∗ WP e {{ v, P1 v ∧ P2 v }}.
  Proof.
    iLöb as "IH" forall (e).
    iIntros "H1 H2".
    iEval (rewrite !wp_unfold /wp_pre) in "H1";
    iEval (rewrite !wp_unfold /wp_pre) in "H2";
    iEval (rewrite !wp_unfold /wp_pre).
    case_match; first by auto.
    iIntros (σ1 k ks n) "#Ha".
    iDestruct ("H1" $! σ1 k ks n with "Ha") as "[$ H1]".
    iDestruct ("H2" $! σ1 k ks n with "Ha") as "[% H2]".
    iIntros (e2 σ2 efs Hstep).
    iSpecialize ("H1" $! e2 σ2 efs Hstep);
    iSpecialize ("H2" $! e2 σ2 efs Hstep).
    iNext.
    iDestruct "H1" as "[$ [H1 $]]".
    iDestruct "H2" as "[_ [H2 _]]".
    by iApply ("IH" with "H1 H2").
  Qed.
End wp_extra.
