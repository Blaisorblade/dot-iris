From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.

From D Require Import proofmode_extra.
From D.Dot Require Import dlang_inst step_fv.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).
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
