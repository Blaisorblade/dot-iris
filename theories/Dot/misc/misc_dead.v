From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.

From D Require Import proofmode_extra.
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
