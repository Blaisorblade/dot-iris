Require Import Dot.tactics.
Require Import Dot.unary_lr.
Require Import Dot.operational.
Import operational.lang.
From iris.program_logic Require Import adequacy.


Section Sec.
  Context `{HdotG: dotG Σ}.

  Theorem adequacy e e' thp σ σ' T ρ:
    (True ⊢ ⟦ T ⟧ₑ ρ e ) →
    rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
    is_Some (to_val e') ∨ reducible e' σ'.
  Proof.
    intros Hlog ??. cut (adequate NotStuck e σ (λ _ _, True)); first (intros [_ ?]; eauto).
    eapply (wp_adequacy Σ); eauto. admit.
    iIntros (Hinv ?). iModIntro. iExists (λ _ _, True%I). iSplit=> //.
    (* rewrite -(empty_env_subst e). *)
    set (HΣ := IrisG _ _ Hinv (λ _ _ _, True)%I (λ _, True)%I).
    iApply (wp_wand with "[]").
    unfold interp_expr in *. simpl in *.
    iAssert (WP e {{ v, (uinterp T) (ρ, v) }})%I as "H".
    iPoseProof Hlog as "HH". simpl. 
    admit.
    iAssumption. iIntros "**". done.
  Admitted.

End Sec.

