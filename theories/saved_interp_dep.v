From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
From D Require Import prelude iris_prelude.

Import uPred EqNotations.
Unset Program Cases.

(* Repeat temporarily-disabled Iris notations. *)
Notation "{ x  &  P }" := (sigTOF (λ x, P%OF)) : oFunctor_scope.
Notation "{ x : A &  P }" := (@sigTOF A%type (λ x, P%OF)) : oFunctor_scope.

(* For Iris. *)
Global Instance projT1_ne {A P}: NonExpansive (projT1: @sigTO A P → leibnizO A).
Proof. solve_proper. Qed.

Global Instance projT1_proper {A P}: Proper ((≡) ==> (≡)) (projT1: @sigTO A P → leibnizO A).
Proof. apply ne_proper, projT1_ne. Qed.

Lemma projT2_ne {A P} n (x1 x2 : @sigTO A P) (Heq : x1 ≡{n}≡ x2):
  rew (sigT_dist_proj1 n Heq) in projT2 x1 ≡{n}≡ projT2 x2.
Proof. by destruct Heq. Qed.

Lemma projT2_proper {A P} `{!∀ a b : A, ProofIrrel (a = b)} :
  ∀ (x1 x2 : @sigTO A P) (Heqs : x1 ≡ x2),
    rew (sigT_equiv_proj1 _ _ Heqs) in projT2 x1 ≡ projT2 x2.
Proof.
  move => [a1 x1] [a2 x2] Heqs.
  case: (proj1 (sigT_equiv_eq_alt _ _) Heqs) => /=. intros ->.
  rewrite (proof_irrel (sigT_equiv_proj1 _ _ Heqs) eq_refl) //.
Qed.

Definition vec n vl := fin n → vl.

Notation pred B C Σ := (B -d> C -d> iProp Σ).
Notation hoPredN n A B C Σ := (vec n A -d> pred B C Σ).

Definition hoPred_P A B C Σ := (λ n, hoPredN n A B C Σ).
Definition hoPredO A B C Σ : ofeT := sigTO (hoPred_P A B C Σ).

Definition hoPredOF A B C : oFunctor := { n & vec n A -d> B -d> C -d> ▶ ∙ }.

Notation savedHoPredG A B C Σ := (savedAnythingG Σ (hoPredOF A B C)).
Notation savedHoPredΣ A B C := (savedAnythingΣ (hoPredOF A B C)).

Definition packedHoPred A B C Σ : ofeT := hoPredOF A B C (iProp Σ) _.



Section saved_ho_sem_type.
  Context {A B C : Type}.
  Context `{!savedHoPredG A B C Σ}.
  Implicit Types (Ψ : packedHoPred A B C Σ).

  Definition packedHoPred_eq : packedHoPred A B C Σ =
    sigTO (λ n, vec n A -d> B -d> C -d> laterO (iProp Σ)) := reflexivity _.

  Definition packedHoPred_arity : packedHoPred A B C Σ -n> natO := λne x, projT1 x.

  Definition cpack n : hoPredN n A B C Σ → packedHoPred A B C Σ :=
    λ Φ, existT n (λ args ρ v, Next (Φ args ρ v)).

  Global Instance cpack_contractive: Contractive (cpack n).
  Proof.
    rewrite /cpack => ?????.
    apply (existT_ne _ eq_refl).
    solve_contractive_ho.
  Qed.

  Program Definition pack : hoPredO A B C Σ -n> packedHoPred A B C Σ :=
    λne Φ, cpack (projT1 Φ) (projT2 Φ).
  Next Obligation.
    move => n [i1 Φ1] [i2 Φ2][/= Heqi HeqΦ]. destruct Heqi. by f_equiv.
  Qed.

  Definition saved_ho_sem_type_own γ n (Φ : hoPredN n A B C Σ) : iProp Σ :=
    saved_anything_own (F := hoPredOF A B C) γ (pack (existT n Φ)).

  Notation "γ ⤇[ n  ] φ" := (saved_ho_sem_type_own γ n φ) (at level 20).

  Instance saved_ho_sem_type_own_contractive γ i : Contractive (saved_ho_sem_type_own γ i).
  Proof.
    rewrite /saved_ho_sem_type_own => n f g /= Heq. f_equiv.
    apply (existT_ne _ eq_refl) => ??? /=.
    solve_contractive_ho.
  Qed.

  Lemma saved_ho_sem_type_alloc i φ : (|==> ∃ γ, γ ⤇[ i ] φ)%I.
  Proof. apply saved_anything_alloc. Qed.

  Lemma packedHoPred_arity_neI Ψ1 Ψ2 : Ψ1 ≡ Ψ2 ⊢@{iPropI Σ}
    packedHoPred_arity Ψ1 ≡ packedHoPred_arity Ψ2.
  Proof. exact: f_equiv. Qed.

  Lemma packedHoPred_arity_neI_pure Ψ1 Ψ2 : Ψ1 ≡ Ψ2 ⊢@{iPropI Σ}
    ⌜ packedHoPred_arity Ψ1 = packedHoPred_arity Ψ2 ⌝.
  Proof. rewrite packedHoPred_arity_neI; auto. Qed.

  Lemma saved_ho_sem_type_agree_arity γ {i j Φ1 Φ2}:
    γ ⤇[ i ] Φ1 -∗ γ ⤇[ j ] Φ2 -∗ ⌜ i = j ⌝.
  Proof.
    iIntros "HΦ1 HΦ2 /=".
    (* iDestruct (packedHoPred_arity_neI_pure with "[HΦ1 HΦ2]") as "?".
    iApply (saved_anything_agree with "HΦ1 HΦ2"). done. *)
    (* Fail iDestruct (packedHoPred_arity_neI_pure $! (saved_anything_agree with "HΦ1 HΦ2")) as "?". *)
    iDestruct (saved_anything_agree with "HΦ1 HΦ2") as "Heq".
    (* iDestruct (packedHoPred_arity_neI_pure with "Heq") as "?". *)
    rewrite packedHoPred_arity_neI_pure. done.
  Qed.

  Lemma saved_ho_sem_type_agree γ n (Φ1 Φ2 : hoPredN n A B C Σ) a b c:
    γ ⤇[ n ] Φ1 -∗ γ ⤇[ n ] Φ2 -∗ ▷ (Φ1 a b c ≡ Φ2 a b c).
  Proof.
    iIntros "HΦ1 HΦ2 /=".
    iDestruct (saved_anything_agree with "HΦ1 HΦ2") as "Heq".
    rewrite /= sigT_equivI. iDestruct "Heq" as (Heq) "Heq".
    rewrite (proof_irrel Heq eq_refl) /=.
    repeat setoid_rewrite bi.discrete_fun_equivI; iNext.
    iApply "Heq".
  Qed.

  Lemma saved_ho_sem_type_agree_dep γ {i j Φ1 Φ2} a b c:
    γ ⤇[ i ] Φ1 -∗ γ ⤇[ j ] Φ2 -∗ ∃ eq : i = j,
    ▷ ((rew [hoPred_P A B C Σ] eq in Φ1) a b c ≡ Φ2 a b c).
  Proof.
    iIntros "HΦ1 HΦ2 /=".
    iDestruct (saved_ho_sem_type_agree_arity with "HΦ1 HΦ2") as %->.
    iExists eq_refl; cbn.
    iApply (saved_ho_sem_type_agree with "HΦ1 HΦ2").
  Qed.
End saved_ho_sem_type.

Notation "γ ⤇[ n  ] φ" := (saved_ho_sem_type_own γ n φ) (at level 20).
Global Opaque saved_ho_sem_type_own.
