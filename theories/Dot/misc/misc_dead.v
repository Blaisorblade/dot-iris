From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.

From D Require Import proofmode_extra.

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
End wp_extra.

From D.Dot Require Import dlang_inst path_wp rules synLemmas step_fv.
Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (p : path)
         (Γ : ctx) (ρ : vls).

Section Sec.
  Context `{HdlangG: dlangG Σ}.

  (* Was also proved for DSub. *)
  Lemma wp_wand_cl e Φ Ψ:
    WP e {{ v, Φ v }} -∗ ⌜ nclosed e 0 ⌝ -∗ (∀ v, Φ v -∗ ⌜ nclosed_vl v 0 ⌝ -∗ Ψ v) -∗ WP e {{ v, Ψ v }}.
  Proof.
    iIntros "/= He" (Hcle) "Himpl". iApply (wp_wand_wf _ _ e Φ (flip nclosed 0) Hcle with "He [Himpl]").
    intros. by eapply nclosed_prim_step.
    iIntros (v Hclv) "/= H". iApply ("Himpl" with "H [%]"). exact: fv_of_val_inv.
  Qed.
End Sec.

Section path_wp.
  Context `{HdlangG: dlangG Σ}.
  Implicit Types (φ : vl -d> iPropO Σ).

  Lemma path_wp_cl n p v:
    path_wp p (λ w, ⌜ w = v ⌝) ⊢@{iPropI Σ}
    ▷^(plength p) ⌜ nclosed p n → nclosed_vl v n ⌝.
  Proof.
    elim: p v => /= [w|p IHp l] v.
    - iIntros "!%" (->). exact: fv_pv_inv.
    - rewrite path_wp_eq -swap_later; setoid_rewrite IHp.
      iDestruct 1 as (w) "[Hpwp H]".
      iNext (plength p).
      iDestruct "Hpwp" as %Himpl.
      iDestruct "H" as (? Hl) "> ->". iIntros "!%" (Hclps).
      enough (nclosed (dvl v) n). by eauto with fv.
      eapply nclosed_lookup', Himpl; eauto with fv.
  Qed.

  Lemma path_wp_timeless_len φ p:
    (∀ v, Timeless (φ v)) →
    path_wp p φ ⊢ ▷^(plength p) False ∨ ∃ v, path_wp p (λ w, ⌜ w = v ⌝) ∧ φ v.
  Proof.
    rewrite path_wp_eq. intros Htime. iDestruct 1 as (v) "(Heq & Hv)".
    iDestruct (timeless_timelessN with "Hv") as "[H | H]"; eauto.
  Qed.

  Fixpoint path2tm p: tm :=
    match p with
    | pv v => tv v
    | pself p l => tproj (path2tm p) l
    end.

  Lemma path_wp_exec p v :
    path_wp p (λ w, ⌜ w = v ⌝) ⊢@{iPropI Σ} ▷^(plength p) ⌜ PureExec True (plength p) (path2tm p) (tv v) ⌝.
  Proof.
    iInduction p as [w|] "IHp" forall (v); rewrite /PureExec/=.
    - iIntros (-> _). by iIntros "!%"; constructor.
    - iIntros "#Hp" (_). iDestruct (path_wp_eq with "Hp") as (vp) "{Hp}(Hp&Hs)".
      iSpecialize ("IHp" with "Hp"). iClear "Hp".
      rewrite -swap_later. iNext (plength p).
      iDestruct "IHp" as %Hpure. iDestruct "Hs" as (vq Hlook) "> ->".
      iIntros "!%". eapply nsteps_r.
      + by apply (pure_step_nsteps_ctx (fill_item (ProjCtx l))), Hpure.
      + apply nsteps_once_inv, pure_tproj, Hlook.
  Qed.

  Lemma path_wp_adequacy p φ :
    (∀ v, Timeless (φ v)) →
    path_wp p φ ⊢ ▷^(plength p) False ∨ (∃ v, ⌜ PureExec True (plength p) (path2tm p) (tv v) ⌝ ∧ φ v).
  Proof.
    intros Htime. rewrite path_wp_timeless_len; iDestruct 1 as "[$|H]".
    iApply timeless_timelessN. setoid_rewrite path_wp_exec. iNext. eauto.
  Qed.
End path_wp.
