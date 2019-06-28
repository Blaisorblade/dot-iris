From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
From D Require Import prelude iris_prelude.

Import uPred EqNotations.
Unset Program Cases.

(* Repeat temporarily-disabled Iris notations. *)
Notation "{ x  &  P }" := (sigTOF (λ x, P%OF)) : oFunctor_scope.
Notation "{ x : A &  P }" := (@sigTOF A%type (λ x, P%OF)) : oFunctor_scope.
Definition vec n vl := fin n → vl.

Notation _envD vl Σ := ((var → vl) -d> vl -d> iProp Σ).
Notation hoEnvND n vl Σ := (vec n vl -d> _envD vl Σ).

Definition hoEnvD_P vl Σ := (λ n, hoEnvND n vl Σ).
Definition hoEnvDO vl Σ : ofeT := sigTO (hoEnvD_P vl Σ).

Definition hoEnvDOF vl : oFunctor := { n & vec n vl -d> (var → vl) -d> vl -d> ▶ ∙ }.

Notation savedHoSemTypeG vl Σ := (savedAnythingG Σ (hoEnvDOF vl)).
Notation savedHoSemTypeΣ vl := (savedAnythingΣ (hoEnvDOF vl)).

Definition packedFun vl Σ : ofeT := hoEnvDOF vl (iProp Σ) _.

(* For Iris. *)
Global Instance projT1_ne {A P}: NonExpansive (projT1: @sigTO A P → leibnizO A).
Proof. solve_proper. Qed.

Lemma projT2_ne {A P}: ∀ n (x1 x2 : @sigTO A P) (Heq : x1 ≡{n}≡ x2),
  rew (sigT_dist_proj1 n Heq) in projT2 x1 ≡{n}≡ projT2 x2.
Proof. by destruct Heq. Qed.

Section saved_ho_sem_type.
  Context `{!savedHoSemTypeG vl Σ}.
  Implicit Types (Ψ : packedFun vl Σ).

  Definition packedFun_eq : packedFun vl Σ =
    sigTO (λ n, vec n vl -d> (var → vl) -d> vl -d> laterO (iProp Σ)) := reflexivity _.

  Definition packedFun_arity : packedFun vl Σ -n> natO := λne x, projT1 x.

  Definition cpack n : hoEnvND n vl Σ → packedFun vl Σ :=
    λ Φ, existT n (λ args ρ v, Next (Φ args ρ v)).

  Global Instance cpack_contractive: Contractive (cpack n).
  Proof.
    rewrite /cpack => ?????.
    apply (existT_ne _ eq_refl).
    solve_contractive_ho.
  Qed.

  Program Definition pack : hoEnvDO vl Σ -n> packedFun vl Σ :=
    λne Φ, cpack (projT1 Φ) (projT2 Φ).
  Next Obligation.
    move => n [i1 Φ1] [i2 Φ2][/= Heqi HeqΦ]. destruct Heqi. by f_equiv.
  Qed.

  Definition saved_ho_sem_type_own γ n (Φ : hoEnvND n vl Σ) : iProp Σ :=
    saved_anything_own (F := hoEnvDOF vl) γ (pack (existT n Φ)).

  Notation "γ ⤇[ n  ] φ" := (saved_ho_sem_type_own γ n φ) (at level 20).

  Instance saved_ho_sem_type_own_contractive γ i : Contractive (saved_ho_sem_type_own γ i).
  Proof.
    rewrite /saved_ho_sem_type_own => n f g /= Heq. f_equiv.
    apply (existT_ne _ eq_refl) => ??? /=.
    solve_contractive_ho.
  Qed.

  Lemma saved_ho_sem_type_alloc i φ : (|==> ∃ γ, γ ⤇[ i ] φ)%I.
  Proof. apply saved_anything_alloc. Qed.

  Lemma packedFun_arity_neI Ψ1 Ψ2 : Ψ1 ≡ Ψ2 ⊢@{iPropI Σ}
    packedFun_arity Ψ1 ≡ packedFun_arity Ψ2.
  Proof. exact: f_equiv. Qed.

  Lemma packedFun_arity_neI2 Ψ1 Ψ2 : Ψ1 ≡ Ψ2 ⊢@{iPropI Σ}
    ⌜ packedFun_arity Ψ1 = packedFun_arity Ψ2 ⌝.
  Proof. rewrite packedFun_arity_neI; auto. Qed.

  Lemma saved_ho_sem_type_agree_arity γ {i j Φ1 Φ2}:
    γ ⤇[ i ] Φ1 -∗ γ ⤇[ j ] Φ2 -∗ ⌜ i = j ⌝.
  Proof.
    iIntros "HΦ1 HΦ2 /=".
    (* iDestruct (packedFun_arity_neI2 with "[HΦ1 HΦ2]") as "?".
    iApply (saved_anything_agree with "HΦ1 HΦ2"). done. *)
    (* Fail iDestruct (packedFun_arity_neI2 $! (saved_anything_agree with "HΦ1 HΦ2")) as "?". *)
    iDestruct (saved_anything_agree with "HΦ1 HΦ2") as "Heq".
    (* iDestruct (packedFun_arity_neI2 with "Heq") as "?". *)
    rewrite packedFun_arity_neI2. done.
  Qed.

  Lemma saved_ho_sem_type_agree γ n (Φ1 Φ2 : hoEnvND n vl Σ) a b c:
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
    ▷ ((rew [hoEnvD_P vl Σ] eq in Φ1) a b c ≡ Φ2 a b c).
  Proof.
    iIntros "HΦ1 HΦ2 /=".
    iDestruct (saved_ho_sem_type_agree_arity with "HΦ1 HΦ2") as %->.
    iExists eq_refl; cbn.
    iApply (saved_ho_sem_type_agree with "HΦ1 HΦ2").
  Qed.
End saved_ho_sem_type.

Notation "γ ⤇[ n  ] φ" := (saved_ho_sem_type_own γ n φ) (at level 20).
Global Opaque saved_ho_sem_type_own.
