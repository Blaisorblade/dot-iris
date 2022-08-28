From D.iris_extra Require Import proofmode_pupd.

Implicit Type (Σ : gFunctors) (E : coPset).

Ltac pupd :=
  iApply elim_pers_modal; iModIntro (□ _)%I;
  iApply (strip_pupd with "[-]").

Section test.
  Context {PROP : bi}.
  Implicit Type (P Q R : PROP).

  Section test_bupd.
    Context `{!BiBUpd PROP}.

    Lemma PB_sep_curry_alt P Q : <PB> P -∗ <PB> Q -∗ <PB> (P ∗ Q).
    Proof.
      iIntros "#P #Q".
      iApply (PB_bind with "P"); iIntros "!> {P}#$".
      iApply (PB_bind with "Q"); iIntros "!> {Q}#$".
      by [].
    Qed.

    (* #[global] Instance elim_pers_modal_int_bupd_int `{BiBUpd PROP} P Q :
      ElimPersModal (pbupd P) (pbupd Q) (□ P) (□ Q).
    Proof.
      rewrite /ElimPersModal.
      iIntros "#W #P !>". iMod "P" as "#P". iIntros "!> !>".
      iApply ("W" with "P").
    Qed. *)

    (* Lemma foo' `{BiPositive PROP} P Q :
      pbupd (P ∗ Q) ⊢ pbupd P ∗ pbupd Q.
    Proof.
      iIntros "#PQ".
      rewrite -intuitionistically_sep. iModIntro.
      iDestruct "PQ" as "[P Q]".
      iApply sep_bupd. iModIntro.
      iMod "P" as "#P". iMod "Q" as "#Q". *)

    (* Meant to strip modalities from all premises, unlike [elim_pers_modal_wand]; but too restrictive. *)
    (* #[global] Instance elim_pers_modal_wand_all P P' R Q Q' :
      ElimPersModal (□ P) (pbupd Q) (□ P') (pbupd Q') →
      ElimPersModal (□ P) (pbupd R -∗ pbupd Q) (□ P') (□ R -∗ pbupd Q').
    Proof.
      rewrite /ElimPersModal.
      iIntros (W) "#W #P #R !>". iMod "R" as "#R".
      iApply (W with "[] P") => {W}.
      iIntros "!> {P} #P".
      iApply ("W" with "P R").
    Qed. *)

    Lemma test_1 P1 Q :
      □(□ P1 -∗ □ Q) -∗
      pbupd P1 -∗ pbupd Q.
      (* ElimPersModal (pbupd P1) (pbupd P2 -∗ pbupd Q) (□ P1) (□ P2 -∗ □ Q) *)
    Proof.
      iIntros "#W".
      pupd.
      iIntros "#P1".
      by iApply "W".
    Restart.
    Proof.
      rewrite -elim_pers_modal.
      iIntros "#W !> #P1 !>!>".
      by iApply "W".
    Qed.

    Lemma test_2 P1 P2 Q :
      □(□ P1 -∗ □ P2 -∗ □ Q) -∗
      pbupd P1 -∗ pbupd P2 -∗ pbupd Q.
      (* ElimPersModal (pbupd P1) (pbupd P2 -∗ pbupd Q) (□ P1) (□ P2 -∗ □ Q) *)
    Proof.
      iIntros "#W".
      pupd.
      iIntros "#P1 #P2".
      by iApply "W".
    Restart.
      iIntros "#W".
      pupd.
      solve [iApply "W"].
    Restart.
    Proof.
      rewrite -elim_pers_modal.
      iIntros "#W !> #P1 #P2 !>!>".
      by iApply "W".
    Qed.

    Lemma test_3 P1 P2 P3 Q :
      □(□ P1 -∗ □ P2 -∗ □ P3 -∗ □ Q) -∗
      pbupd P1 -∗ pbupd P2 -∗ pbupd P3 -∗ pbupd Q.
      (* ElimPersModal (pbupd P1) (pbupd P2 -∗ pbupd Q) (□ P1) (□ P2 -∗ □ Q) *)
    Proof.
      iIntros "#W".
      pupd.
      iIntros "#P1 #P2 #P3".
      by iApply "W".
    Restart.
    Proof.
      rewrite -elim_pers_modal.
      iIntros "#W !> #P1 #P2 #P3 !>!>".
      by iApply "W".
    Qed.

    Lemma test_2'' (P P' R Q Q' : PROP) `{!Persistent P', !Affine P'} :
      ElimPersModal P Q P' Q' →
      ElimPersModal P (R -∗ Q) P' (R -∗ Q').
    Proof.
      rewrite /ElimPersModal.
      iIntros (W) "#W P R".
      iApply (W with "[R] P").
      rewrite wand_curry (comm _ P' R) -wand_curry.
      iSpecialize ("W" with "R").
      Fail iApply "W".
    Abort.

    Section test_alt_setup.
      #[local] Remove Hints elim_pers_modal_wand_noelim elim_pers_modal_wand_elim : typeclass_instances.

      (* Variant of [elim_modal_wand]. Meant to only strip modalities from one premise. *)
      #[local] Instance elim_pers_modal_wand P P' R Q Q' `{!Persistent R, !Affine R} :
        ElimPersModal P Q P' Q' →
        ElimPersModal P (R -∗ Q) P' (R -∗ Q') | 100.
      Proof.
        rewrite /ElimPersModal.
        iIntros (W) "#W P #R".
        iApply (W with "[] P").
        rewrite wand_curry (comm _ P' R) -wand_curry.
        iApply ("W" with "R").
      Qed.

      Lemma test_2_alt (P1 P2 Q : PROP) :
        □(□ P1 -∗ □ P2 -∗ □ Q) -∗
        pbupd P1 -∗ pbupd P2 -∗ pbupd Q.
        (* ElimPersModal (pbupd P1) (pbupd P2 -∗ pbupd Q) (□ P1) (□ P2 -∗ □ Q) *)
      Proof.
        iIntros "#W".
        iApply elim_pers_modal; iIntros "!> #P1".
        iApply elim_pers_modal; iIntros "!> #P2".
        iIntros "!> !>".
        by iApply "W".
      Restart.
      Proof.
        iIntros "#W #P1".
        iApply (@elim_pers_modal _ (pbupd P2) (pbupd Q)).
        iIntros "!> #P2 !>".
        iMod "P1".
        iApply ("W" with "P1 P2").
      Restart.
      Proof.
        (* apply /elim_pers_modal_wand.
        rewrite /ElimPersModal. *)
        iIntros "#W #P1 #P2 !>".
        iMod "P1" as "#P1".
        iMod "P2" as "#P2".
        iIntros "!> !>".
        iApply ("W" with "P1 P2").
      Qed.
    End test_alt_setup.

    Section misc_tests.
      Context {Σ}.

      Instance foo1 (p : bool) P Q : ElimModal True p false (□ |==> P) P (|==> Q) (|==> Q).
      Proof.
        rewrite /ElimModal/= intuitionistically_if_elim.
        iIntros (_) "[#>A W]".
        iApply ("W" with "A").
      Qed.

    (*
      Instance foo2 (P Q : iProp Σ) : ElimModal True false false (□ |==> P) P (□ |==> Q) (□ |==> Q).
      Proof.
        rewrite /ElimModal/=.
        iIntros (_) "[#A W]".
        iApply ("W" with "[-]").
      Qed. *)

      Instance foo3 (P Q : iProp Σ) : ElimModal True false false (pbupd P) P (pbupd Q) (pbupd Q).
      Proof.
        rewrite /ElimModal/=.
        iIntros (_) "[#A W] !>".
        Fail iApply ("W" with "[-]").
      Abort.

      (*
      Instance foo2 (P Q : iProp Σ) : ElimModal True false false (□ |==> □ P) P (□ |==> □ Q) (□ |==> □ Q).
      Proof.
        rewrite /ElimModal/=.
        iIntros (_) "[#A W]".
        iApply ("W" with "[-]").
      Qed. *)

    End misc_tests.
  End test_bupd.

  Section test_fupd.
    Context `{!BiFUpd PROP} E.

    Lemma test_fupd P Q :
      □(□ P -∗ □ Q) -∗
      pfupd E P -∗ pfupd E Q.
    Proof.
      iIntros "#W #P !>". iMod "P" as "#P". iIntros "!> !>".
      iApply ("W" with "P").
    Qed.

    (* Lemma foo' `{BiPositive PROP} P Q :
      pfupd E (P ∗ Q) ⊢ pfupd E P ∗ pfupd E Q.
    Proof.
      iIntros "#PQ".
      rewrite -intuitionistically_sep. iModIntro.
      iDestruct "PQ" as "[P Q]".
      iApply sep_fupd. iModIntro.
      iMod "P" as "#P". iMod "Q" as "#Q". *)

    Lemma fupd_test_1 P1 Q :
      □(□ P1 -∗ □ Q) -∗
      pfupd E P1 -∗ pfupd E Q.
    Proof.
      iIntros "#W".
      pupd.
      iIntros "#P1".
      by iApply "W".
    Restart.
    Proof.
      iIntros "#W".
      pupd.
      solve [iApply "W"].
    Restart.
    Proof.
      rewrite -elim_pers_modal.
      iIntros "#W !> #P1 !>!>".
      by iApply "W".
    Qed.

    Lemma fupd_test_2 P1 P2 Q :
      □(□ P1 -∗ □ P2 -∗ □ Q) -∗
      pfupd E P1 -∗ pfupd E P2 -∗ pfupd E Q.
    Proof.
      iIntros "#W".
      pupd.
      iIntros "#P1 #P2".
      by iApply "W".
    Restart.
    Proof.
      rewrite -elim_pers_modal.
      iIntros "#W !> #P1 #P2 !>!>".
      by iApply "W".
    Qed.

    Lemma fupd_test_3 P1 P2 P3 Q :
      □(□ P1 -∗ □ P2 -∗ □ P3 -∗ □ Q) -∗
      pfupd E P1 -∗ pfupd E P2 -∗ pfupd E P3 -∗ pfupd E Q.
    Proof.
      iIntros "#W".
      pupd.
      iIntros "#P1 #P2 #P3".
      by iApply "W".
    Restart.
    Proof.
      rewrite -elim_pers_modal.
      iIntros "#W !> #P1 #P2 #P3 !>!>".
      by iApply "W".
    Qed.
  End test_fupd.
End test.
