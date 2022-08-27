(** * Automation for the "persistent update" modalities.
This reduces goal like [⊢ <PB> P1 -∗ <PB> P2 -∗ <PB> Q] to
[⊢ □ P1 -* □ P2 -∗ □ Q], by running all ghost updates and (optionally)
introducing the ghost update modality. Support for [<PF{E}>] works similarly, so
we focus on [<PB>] in these docs.

We use custom automation, because [iMod] and [ElimModal] do not allow performing
ghost updates when the goal starts with the [□ |==>] modalities, so tactics like
[iIntros "#>#P1 #>#P2"] do not work and cannot be supported via [ElimModal]
instances.

The fundamental reason is that [<PB>] is only a monad over intuitionistic propositions,
so goals like
<<
  <PB> P1 -∗ <PB> P2 -∗ <PB> Q
>>
reduce to boxed wands like
<<
  □ (□ P1 -* □ P2 -∗ <PB> Q)
>>
but [ElimModal] does not allow generating boxed wands:
<<
Class ElimModal {PROP : bi} (φ : Prop) (p p' : bool) (P P' : PROP) (Q Q' : PROP) :=
  elim_modal : φ → □?p P ∗ (□?p' P' -∗ Q') ⊢ Q.
>>
*)
From D Require Export iris_prelude iris_extra.pupd.

Implicit Type (Σ : gFunctors) (E : coPset).

Class ElimPersModal {PROP : bi} (P Q P' Q' : PROP) :=
  elim_pers_modal : (□(P' -∗ Q') ⊢ P -∗ Q).
#[global] Hint Mode ElimPersModal + + + - - : typeclass_instances.
#[global] Arguments elim_pers_modal {_}.

Section instances.
  Context {PROP : bi}.
  Implicit Type (P Q R : PROP).

  (* Fallback to allow skipping intuitionistic hypotheses *)
  #[global] Instance elim_pers_modal_wand_noelim P Q Q' R R' `{!Persistent P, !Affine P} :
    ElimPersModal Q R Q' R' →
    ElimPersModal P (Q -∗ R) P (Q' -∗ R') | 50.
  Proof.
    rewrite /ElimPersModal.
    iIntros (W) "#W #P Q".
    iApply (W with "(W P) Q").
  Qed.

  Section bupd.
    Context `{!BiBUpd PROP}.

    #[global] Instance elim_pers_modal_int_bupd_int P R :
      ElimPersModal (<PB> P) (<PB> R) (□ P) (<PB> R).
    Proof.
      rewrite /ElimPersModal.
      iIntros "W P". iApply (PB_bind with "P W").
    Qed.

    (* Meant to strip modalities from all premises, unlike [elim_pers_modal_wand].
    Alternative to [elim_pers_modal_wand_all] *)
    #[global] Instance elim_pers_modal_wand_elim P Q R R' :
      (∀ Q, ElimPersModal (<PB> Q) R (□ Q) R') →
      ElimPersModal (<PB> P) (<PB> Q -∗ R) (□ P) (□ Q -∗ R').
    Proof.
      rewrite /ElimPersModal.
      iIntros (W) "#W #P #Q".
      iApply (W (P ∧ Q)%I). {
        iIntros "!> {P Q} #[P Q]".
        iApply ("W" with "P Q").
      }
      iApply (PB_and_curry with "P Q").
    Qed.
  End bupd.

  Section fupd.
    Context `{!BiFUpd PROP} E.

    #[global] Instance elim_pers_modal_int_fupd_int P R :
      ElimPersModal (<PF{E}> P) (<PF{E}> R) (□ P) (<PF{E}> R).
    Proof.
      rewrite /ElimPersModal.
      iIntros "W P". iApply (PF_bind with "P W").
    Qed.

    (* Meant to strip modalities from all premises, unlike [elim_pers_modal_wand].
    Alternative to [elim_pers_modal_wand_all] *)
    #[global] Instance elim_pers_modal_fupd_wand_elim P Q R R' :
      (∀ Q, ElimPersModal (<PF{E}> Q) R (□ Q) R') →
      ElimPersModal (<PF{E}> P) (<PF{E}> Q -∗ R) (□ P) (□ Q -∗ R').
    Proof.
      rewrite /ElimPersModal.
      iIntros (W) "#W #P #Q".
      iApply (W (P ∧ Q)%I). {
        iIntros "!> {P Q} #[P Q]".
        iApply ("W" with "P Q").
      }
      iApply (PF_and_curry with "P Q").
    Qed.
  End fupd.
End instances.
