(** * Iris saved predicates. *)
From iris.base_logic Require Import lib.saved_prop.
From stdpp Require Import vector.
From D Require Import prelude iris_prelude asubst_intf.

Set Suggest Proof Using.
Set Default Proof Using "Type".

Import EqNotations.
Unset Program Cases.

Notation anil := vector.vnil.
Section vec.
  Context {vl : Type} {n : nat} {A : ofeT}.
  (* vector operations, on a functional representation of vectors. *)
  Definition vcons (v : vl) (args: vec vl n) : vec vl (S n) := vector.vcons v args.

  Definition vhead (args: vec vl (S n)) : vl := args !!! 0%fin.
  Definition vtail (args: vec vl (S n)) : vec vl n :=
    Vector.caseS (λ n _, vec vl n) (λ h n t, t) args.

  Lemma vec_anil_eta (v : vec vl 0) : v = anil.
  Proof. by apply vec_0_inv with (P := λ v, v = anil). Qed.

  Lemma vec_vcons_eta : ∀ args : vec vl (S n),
    vcons (vhead args) (vtail args) = args.
  Proof. exact: vec_S_inv. Qed.

  (** Manipulation of higher-order semantic types. *)
  Definition vopen (Φ : A) : vec vl 0 -d> A := λ args, Φ.
  #[global] Arguments vopen /.

  Definition vcurry (Φ : vec vl (S n) -d> A) : vl -d> vec vl n -d> A :=
    λ v args, Φ (vcons v args).

  Definition vuncurry (Φ : vl -d> vec vl n -d> A) : vec vl (S n) -d> A :=
    λ args, Φ (vhead args) (vtail args).
End vec.

Instance vcurry_ne vl n A m :
  Proper (dist m ==> (=) ==> dist m) (@vcurry vl n A).
Proof. solve_proper_ho. Qed.

Instance vcurry_proper vl n A : Proper ((≡) ==> (=) ==> (≡)) (@vcurry vl n A).
Proof. solve_proper_ho. Qed.
Instance: Params (@vcurry) 3 := {}.

Definition vec_fold {A} {P : nat → Type}
  (base : P 0) (step : ∀ {n}, A → P n → P (S n)) : ∀ n, vec A n → P n :=
  fix rec n :=
    match n with
    | 0 =>   λ argTs, base
    | S n => λ argTs, step (vhead argTs) (rec n (vtail argTs))
    end.

Module Type SavedInterpDep (Import V : VlSortsSig).

Notation envPred s Σ := (env -d> s -d> iPropO Σ).
Notation envD Σ := (envPred vl Σ).
Definition hoEnvPred s Σ n := vec vl n -d> envPred s Σ.
Notation hoEnvD := (hoEnvPred vl).

Definition hoEnvPredO s Σ : ofeT := sigTO (hoEnvPred s Σ).
Definition hoEnvPredOF s : oFunctor := { n & vec vl n -d> env -d> s -d> ▶ ∙ }.

Definition packedHoEnvPred s Σ : ofeT := oFunctor_apply (hoEnvPredOF s) (iPropO Σ).
Definition packedHoEnvD Σ := packedHoEnvPred vl Σ.

Definition hoD Σ n := vec vl n -d> vl -d> iPropO Σ.

Notation savedHoEnvPredG s Σ := (savedAnythingG Σ (hoEnvPredOF s)).
Notation savedHoEnvPredΣ s := (savedAnythingΣ (hoEnvPredOF s)).

Section saved_ho_sem_type.
  Context {s : Type}.
  Context `{!savedHoEnvPredG s Σ}.
  Implicit Types (Ψ : packedHoEnvPred s Σ).

  Definition packedHoEnvPred_arity : packedHoEnvPred s Σ -n> natO := λne x, projT1 x.

  Definition ho_cpack n : hoEnvPred s Σ n → packedHoEnvPred s Σ :=
    λ Φ, existT n (λ args ρ v, Next (Φ args ρ v)).

  #[global] Instance cpack_contractive n : Contractive (ho_cpack n).
  Proof.
    rewrite /ho_cpack /hoEnvPred => ????.
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
  Notation "γ ⤇n[ n  ] φ" := (saved_ho_sem_type_own γ n φ) (at level 20).

  #[global] Instance saved_ho_sem_type_own_contractive γ i :
    Contractive (saved_ho_sem_type_own γ i).
  Proof.
    rewrite /saved_ho_sem_type_own /hoEnvPred => n f g /= Heq. f_equiv.
    apply (existT_ne _ eq_refl) => ??? /=.
    solve_contractive_ho.
  Qed.

  Lemma saved_ho_sem_type_alloc i φ : ⊢ |==> ∃ γ, γ ⤇n[ i ] φ.
  Proof. apply saved_anything_alloc. Qed.

  Lemma leibniz_equivI (PROP : bi) `{LeibnizEquiv A} x y : ⌜ x ≡@{A} y ⌝ ⊢@{PROP} ⌜ x = y ⌝.
  Proof. iIntros "!%". apply leibniz_equiv. Qed.

  Lemma saved_ho_sem_type_agree_arity γ {i j Φ1 Φ2}:
    γ ⤇n[ i ] Φ1 -∗ γ ⤇n[ j ] Φ2 -∗ ⌜ i = j ⌝.
  Proof.
    rewrite -leibniz_equivI -discrete_eq; iIntros "HΦ1 HΦ2".
    iDestruct (saved_anything_agree with "HΦ1 HΦ2") as "Heq".
    iApply (f_equivI packedHoEnvPred_arity with "Heq").
  Qed.

  Lemma saved_ho_sem_type_agree_dep_abs γ {i j Φ1 Φ2}:
    γ ⤇n[ i ] Φ1 -∗ γ ⤇n[ j ] Φ2 -∗ ∃ Heq : i = j,
    ▷ ((rew [hoEnvPred s Σ] Heq in Φ1) ≡ Φ2).
  Proof.
    iIntros "HΦ1 HΦ2".
    iDestruct (saved_ho_sem_type_agree_arity with "HΦ1 HΦ2") as %->.
    iExists eq_refl; cbn.
    iDestruct (saved_anything_agree with "HΦ1 HΦ2") as "Heq".
    rewrite /= sigT_equivI. iDestruct "Heq" as (Heq) "Hgoal".
    rewrite (proof_irrel Heq eq_refl) /=.
    repeat setoid_rewrite discrete_fun_equivI. by iNext.
  Qed.

  Lemma saved_ho_sem_type_agree_dep {γ i j Φ1 Φ2} a b c:
    γ ⤇n[ i ] Φ1 -∗ γ ⤇n[ j ] Φ2 -∗ ∃ Heq : i = j,
    ▷ ((rew [hoEnvPred s Σ] Heq in Φ1) a b c ≡ Φ2 a b c).
  Proof.
    iIntros "HΦ1 HΦ2".
    iDestruct (saved_ho_sem_type_agree_dep_abs with "HΦ1 HΦ2") as (->) "Hgoal".
    iExists eq_refl; cbn; iNext.
    by repeat setoid_rewrite discrete_fun_equivI.
  Qed.

  Lemma saved_ho_sem_type_agree γ n (Φ1 Φ2 : hoEnvPred s Σ n) a b c:
    γ ⤇n[ n ] Φ1 -∗ γ ⤇n[ n ] Φ2 -∗ ▷ (Φ1 a b c ≡ Φ2 a b c).
  Proof.
    iIntros "HΦ1 HΦ2".
    iDestruct (saved_ho_sem_type_agree_dep a b c with "HΦ1 HΦ2") as (Heq) "Hgoal".
    by rewrite (proof_irrel Heq eq_refl) /=.
  Qed.

  (* Lemma saved_ho_sem_type_agree_abs γ n (Φ1 Φ2 : hoEnvPred s Σ n):
    γ ⤇n[ n ] Φ1 -∗ γ ⤇n[ n ] Φ2 -∗ ▷ (Φ1 ≡ Φ2).
  Proof.
    iIntros "HΦ1 HΦ2".
    iDestruct (saved_ho_sem_type_agree_dep_abs with "HΦ1 HΦ2") as (Heq) "Hgoal".
    by rewrite (proof_irrel Heq eq_refl) /=.
  Qed. *)
End saved_ho_sem_type.

Notation "γ ⤇n[ n  ] φ" := (saved_ho_sem_type_own γ n φ) (at level 20).
#[global] Opaque saved_ho_sem_type_own.

End SavedInterpDep.
