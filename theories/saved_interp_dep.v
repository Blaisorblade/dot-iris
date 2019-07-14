From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
From D Require Import prelude iris_prelude.

Import EqNotations.
Unset Program Cases.

(* Repeat temporarily-disabled Iris notations. *)
Notation "{ x  &  P }" := (sigTOF (λ x, P%OF)) : oFunctor_scope.
Notation "{ x : A &  P }" := (@sigTOF A%type (λ x, P%OF)) : oFunctor_scope.

Definition vec vl n := fin n → vl.

Section vec.
  Context {vl : Type} {n : nat} {A : ofeT}.
  (* vector operations, on a functional representation of vectors. *)
  Definition vcons (v : vl) (args: vec vl n) : fin (S n) → vl :=
    λ i,
      match i in fin (S n0) with
      | Fin.F1 => λ _, v
      | Fin.FS i' => λ args', args' i'
      end args.

  Definition vnil : vec vl 0 := Fin.case0 _.
  Definition vhead (args: vec vl (S n)) : vl := args Fin.F1.
  Definition vtail (args: vec vl (S n)) : fin n → vl :=
    λ i, args (Fin.FS i).

  (* Manipulation of higher-order semantic types. *)
  Definition vclose (Φ : vec vl 0 -d> A): A := Φ vnil.
  Definition vopen (Φ : A) : vec vl 0 -d> A := λ args, Φ.

  Definition vcurry (Φ : vec vl (S n) -d> A) : vl -d> vec vl n -d> A :=
    λ v args, Φ (vcons v args).

  Definition vuncurry (Φ : vl -d> vec vl n -d> A) : vec vl (S n) -d> A :=
    λ args, Φ (vhead args) (vtail args).
End vec.

Module Type ValueTSig. Parameter vl : Type. End ValueTSig.

Module Type SavedInterpDep (Import V : ValueTSig).

Definition env := var -> vl.
Notation envPred s Σ := (env -d> s -d> iProp Σ).
Definition hoEnvPred s Σ n := vec vl n -d> envPred s Σ.
Definition hoEnvPredO s Σ : ofeT := sigTO (hoEnvPred s Σ).
Definition hoEnvPredOF s : oFunctor := { n & vec vl n -d> env -d> s -d> ▶ ∙ }.
Definition packedHoEnvPred s Σ : ofeT := hoEnvPredOF s (iProp Σ) _.

Definition hoD Σ n := vec vl n -d> vl -d> iProp Σ.
Notation hoEnvD := (hoEnvPred vl).
Notation envD Σ := (envPred vl Σ).
Definition packedHoEnvD Σ := packedHoEnvPred vl Σ.

Notation savedHoEnvPredG s Σ := (savedAnythingG Σ (hoEnvPredOF s)).
Notation savedHoEnvPredΣ s := (savedAnythingΣ (hoEnvPredOF s)).

Section saved_ho_sem_type.
  Context {s : Type}.
  Context `{!savedHoEnvPredG s Σ}.
  Implicit Types (Ψ : packedHoEnvPred s Σ).

  Definition packedHoEnvPred_eq : packedHoEnvPred s Σ =
    sigTO (λ n, vec vl n -d> env -d> s -d> laterO (iProp Σ)) := reflexivity _.

  Definition packedHoEnvPred_arity : packedHoEnvPred s Σ -n> natO := λne x, projT1 x.

  Definition ho_cpack n : hoEnvPred s Σ n → packedHoEnvPred s Σ :=
    λ Φ, existT n (λ args ρ v, Next (Φ args ρ v)).

  Global Instance cpack_contractive: Contractive (ho_cpack n).
  Proof.
    rewrite /ho_cpack /hoEnvPred => ?????.
    apply (existT_ne _ eq_refl).
    solve_contractive_ho.
  Qed.

  Program Definition ho_pack : hoEnvPredO s Σ -n> packedHoEnvPred s Σ :=
    λne Φ, ho_cpack (projT1 Φ) (projT2 Φ).
  Next Obligation.
    move => n [i1 Φ1] [i2 Φ2][/= Heqi HeqΦ]. destruct Heqi. by f_equiv.
  Qed.

  Definition saved_ho_sem_type_own γ n (Φ : hoEnvPred s Σ n) : iProp Σ :=
    saved_anything_own (F := hoEnvPredOF s) γ (ho_pack (existT n Φ)).
  Notation "γ ⤇[ n  ] φ" := (saved_ho_sem_type_own γ n φ) (at level 20).

  Global Instance saved_ho_sem_type_own_persistent γ n φ :
    Persistent (γ ⤇[ n ] φ) := _.

  Global Instance saved_ho_sem_type_own_contractive γ i :
    Contractive (saved_ho_sem_type_own γ i).
  Proof.
    rewrite /saved_ho_sem_type_own /hoEnvPred => n f g /= Heq. f_equiv.
    apply (existT_ne _ eq_refl) => ??? /=.
    solve_contractive_ho.
  Qed.

  Lemma saved_ho_sem_type_alloc i φ : (|==> ∃ γ, γ ⤇[ i ] φ)%I.
  Proof. apply saved_anything_alloc. Qed.

  Lemma packedHoEnvPred_arity_neI Ψ1 Ψ2 : Ψ1 ≡ Ψ2 ⊢@{iPropI Σ}
    packedHoEnvPred_arity Ψ1 ≡ packedHoEnvPred_arity Ψ2.
  Proof. exact: f_equiv. Qed.

  Lemma packedHoEnvPred_arity_neI_pure Ψ1 Ψ2 : Ψ1 ≡ Ψ2 ⊢@{iPropI Σ}
    ⌜ packedHoEnvPred_arity Ψ1 = packedHoEnvPred_arity Ψ2 ⌝.
  Proof. rewrite packedHoEnvPred_arity_neI; auto. Qed.

  Lemma saved_ho_sem_type_agree_arity γ {i j Φ1 Φ2}:
    γ ⤇[ i ] Φ1 -∗ γ ⤇[ j ] Φ2 -∗ ⌜ i = j ⌝.
  Proof.
    iIntros "HΦ1 HΦ2 /=".
    (* iDestruct (packedHoEnvPred_arity_neI_pure with "[HΦ1 HΦ2]") as "?".
    iApply (saved_anything_agree with "HΦ1 HΦ2"). done. *)
    (* Fail iDestruct (packedHoEnvPred_arity_neI_pure $! (saved_anything_agree with "HΦ1 HΦ2")) as "?". *)
    iDestruct (saved_anything_agree with "HΦ1 HΦ2") as "Heq".
    (* iDestruct (packedHoEnvPred_arity_neI_pure with "Heq") as "?". *)
    rewrite packedHoEnvPred_arity_neI_pure. done.
  Qed.

  Lemma saved_ho_sem_type_agree γ n (Φ1 Φ2 : hoEnvPred s Σ n) a b c:
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
    ▷ ((rew [hoEnvPred s Σ] eq in Φ1) a b c ≡ Φ2 a b c).
  Proof.
    iIntros "HΦ1 HΦ2 /=".
    iDestruct (saved_ho_sem_type_agree_arity with "HΦ1 HΦ2") as %->.
    iExists eq_refl; cbn.
    iApply (saved_ho_sem_type_agree with "HΦ1 HΦ2").
  Qed.
End saved_ho_sem_type.

Notation "γ ⤇n[ n  ] φ" := (saved_ho_sem_type_own γ n φ) (at level 20).
Global Opaque saved_ho_sem_type_own.

End SavedInterpDep.
