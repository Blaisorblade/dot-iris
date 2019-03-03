From iris.proofmode Require Import tactics.
From iris.bi Require Import bi tactics.
From iris.proofmode Require Import base modality_instances classes class_instances_bi ltac_tactics.
Import bi.

Module Test_Fail.
  Section foo.
    Context {PROP : sbi}.
    Implicit Types P Q R : PROP.

    Lemma demo_laterN_forall P Q n: (▷^n ∀ x: string, P) -∗ (▷^n ∀ x: string, Q).
    Proof.
      iIntros "H". Fail iIntros (w).
      Fail iSpecialize ("H" $! "a").
    Abort.
  End foo.
End Test_Fail.

Section proofmode_extra.
  Context {PROP : sbi}.
  Implicit Types P Q R : PROP.

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
