(** Automation for the "Persistent Update" modality. *)
From D Require Export iris_prelude.

Implicit Type (Σ : gFunctors) (E : coPset).

(** * "Persistent updates".
[<PB> P] is an intuitionistic propositon that allows allocating persistent ghost
state before proving [P].
*)
Notation pbupd P := (□ |==> □ P)%I.
Notation pfupd E P := (□ |={E}=> □ P)%I.
Notation "<PB> P" := (pbupd P) (at level 20, right associativity).
Notation "<PF{ E }> P" := (pfupd E P) (at level 20, right associativity).

Section persistent_updates.
  Context {PROP : bi}.
  Implicit Type (P Q R : PROP).

  Section bupd.
    Context `{!BiBUpd PROP}.

    (* [<PB>] is a monad on the subcategory of intuitionistic propositions. *)
    Lemma PB_return P : □ P -∗ <PB> P.
    Proof. by iIntros "#$". Qed.

    Lemma PB_bind P Q : <PB> P -∗ □ (□ P -∗ <PB> Q) -∗ <PB> Q.
    Proof.
      iIntros "#P #W !>". iMod "P" as "#P".
      iApply ("W" with "P").
    Qed.

    Lemma PB_join P : <PB> <PB> P -∗ <PB> P.
    Proof. iIntros "#P !>". by iMod "P". Qed.

    (* [<PB>] distributes over conjunctions. *)

    Lemma PB_sep_curry P Q : <PB> P -∗ <PB> Q -∗ <PB> (P ∗ Q).
    Proof.
      iIntros "#P #Q !>".
      by iMod "P" as "#$"; iMod "Q" as "#$".
    Qed.

    Lemma PB_sep P Q : <PB> P ∗ <PB> Q -∗ <PB> (P ∗ Q).
    Proof. iIntros "[P Q]". iApply (PB_sep_curry with "P Q"). Qed.

    Lemma PB_and P Q : <PB> P ∧ <PB> Q -∗ <PB> (P ∧ Q).
    Proof.
      iIntros "[#P #Q] !>".
      iMod "P" as "#P". iMod "Q" as "#Q".
      by iFrame "#".
    Qed.

    Lemma PB_and_curry P Q : <PB> P -∗ <PB> Q -∗ <PB> (P ∧ Q).
    Proof. iIntros "P Q". iApply PB_and. iFrame. Qed.
  End bupd.

  Section fupd.
    Context `{!BiFUpd PROP} E.

    (* [<PF{E}>] is a monad on the subcategory of intuitionistic propositions. *)
    Lemma PF_return P : □ P -∗ <PF{E}> P.
    Proof. by iIntros "#$". Qed.

    Lemma PF_bind P Q : <PF{E}> P -∗ □ (□ P -∗ <PF{E}> Q) -∗ <PF{E}> Q.
    Proof.
      iIntros "#P #W !>". iMod "P" as "#P".
      iApply ("W" with "P").
    Qed.

    Lemma PF_join P : <PF{E}> <PF{E}> P -∗ <PF{E}> P.
    Proof. iIntros "#P !>". by iMod "P". Qed.

    (* [<PF>] distributes over conjunctions. *)
    Lemma PF_sep P Q : <PF{E}> P ∗ <PF{E}> Q -∗ <PF{E}> (P ∗ Q).
    Proof.
      iIntros "[#P #Q] !>".
      iMod "P" as "#P". iMod "Q" as "#Q".
      by iFrame "#".
    Qed.

    Lemma PF_sep_curry P Q : <PF{E}> P -∗ <PF{E}> Q -∗ <PF{E}> (P ∗ Q).
    Proof. iApply wand_curry. iApply PF_sep. Qed.

    Lemma PF_and P Q : <PF{E}> P ∧ <PF{E}> Q -∗ <PF{E}> (P ∧ Q).
    Proof.
      iIntros "[#P #Q] !>".
      iMod "P" as "#P". iMod "Q" as "#Q".
      by iFrame "#".
    Qed.

    Lemma PF_and_curry P Q : <PF{E}> P -∗ <PF{E}> Q -∗ <PF{E}> (P ∧ Q).
    Proof. iIntros "P Q". iApply PF_and. iFrame. Qed.
  End fupd.
End persistent_updates.
