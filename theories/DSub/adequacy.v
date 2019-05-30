From D.pure_program_logic Require Import adequacy.
From iris.proofmode Require Import tactics.
From D Require Import tactics swap_later_impl.
From D.DSub Require Import unary_lr.
Require Import Program.
Import dlang_adequacy.
From D Require Import locAsimpl.

Theorem adequacy Σ `{HdsubG: dlangPreG Σ} `{!SwapProp (iPropSI Σ)} e e' thp σ σ' T ρ:
  (forall `{dsubG Σ} `{SwapProp (iPropSI Σ)}, True ⊢ ⟦ T ⟧ₑ ρ e) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hlog.
  eapply dlang_adequacy.adequacy => // Hdlang Hswap.

  iDestruct (Hlog (DsubG _ _) with "[#//]") as "H".
  (* apply (DsubG _ _). *)
  iIntros "_ !> !>".
  rewrite hsubst_id /=.
  cbn.
  Fail iApply "H".
  Restart.

  intros Hlog.
  eapply dlang_adequacy.adequacy => // Hdlang Hswap.

  iDestruct (Hlog with "[#//]") as "H".
  (* apply (DsubG _ _). *)
  iIntros "_ !> !>".
  rewrite hsubst_id /=.
  iApply "H".
  Unshelve. apply DsubG.
  Restart.

  intros Hlog ??. cut (adequate NotStuck e σ (λ _ _, True)); first (intros [_ ?]; eauto).
  eapply (wp_adequacy Σ) => /=.
  iMod (gen_iheap_init (hG := dlangPreG_interpNames) ∅) as (g) "H".
  iIntros (?) "!>". iExists (λ _ _, True%I); iSplit=> //.
  set (DLangΣ := DLangG Σ _ g).
  Existing Instance DsubG.
  (* Coercion DsubG : dlangG >-> dsubG. *)
  iApply wp_wand; by [iApply (Hlog _) | auto].
Qed.

(* Instance CmraSwappable_dsub: CmraSwappable (iResUR dlangΣ).
Proof.
  apply Swappable_iResUR.
  rewrite /gid; repeat (dependent destruction i; cbn; try apply _).
Qed. *)

(* Instead of still assuming semantic typing, here we should assume syntactic
   typing and use the fundamental lemma. But otherwise this follows the general
   instantiation pattern, from e.g.
   https://gitlab.mpi-sws.org/iris/examples/blob/a89dc12821b63eeb9b831d21629ac55ebd601f38/theories/logrel/F_mu_ref/soundness.v#L29-39. *)
Corollary almost_type_soundness e e' thp σ σ' T:
  (forall `{dsubG Σ} `{SwapProp (iPropSI Σ)}, True ⊢ ⟦ T ⟧ₑ [] e) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros; eapply (adequacy dlangΣ) => //.
  exact: H.
  (* by apply fundamental. *)
Qed.
