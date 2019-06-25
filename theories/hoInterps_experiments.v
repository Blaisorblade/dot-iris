From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
From D Require Import prelude iris_prelude saved_interp_n.

Unset Program Cases.
(* Repeat temporarily-disabled Iris notations. *)
Notation "{ x  &  P }" := (sigTOF (λ x, P%OF)) : oFunctor_scope.
Notation "{ x : A &  P }" := (@sigTOF A%type (λ x, P%OF)) : oFunctor_scope.

Module try1.
Section saved_pred3_use.
  Context {vl : Type} {Σ : gFunctors}.

  Notation envD Σ := ((var → vl) -d> vl -d> iProp Σ).
  Notation hoEnvD Σ := (list vl -d> envD Σ).
  Implicit Types (Φ : hoEnvD Σ) (n : nat).
  Definition eFalse : envD Σ := λ ρ v, False%I.

  (* We can track function arity by just storing a number,
     but that's a bit cumbersome. *)
  Definition hoEnvND Σ : Type := nat * hoEnvD Σ.
  Definition beta : hoEnvND Σ → vl → hoEnvND Σ := λ '(n, Φ) a,
    match n with
    | 0 => (0, λ _, eFalse)
    | S n => (n, λ args, Φ (a :: args))
    end%I.
  Definition close : hoEnvND Σ → envD Σ := λ '(n, Φ), Φ [].
  Definition lambda n (Φ : vl → hoEnvD Σ) : hoEnvND Σ :=
    (n + 1, λ args,
      match args with
      | w :: args => Φ w args
      | [] => eFalse
      end%I).
End saved_pred3_use.
End try1.

Module try2.

Definition vec n vl := fin n → vl.
Section vec.
  Context {vl : Type}.
  (* vector operations, on a functional representation of vectors. *)
  Definition vcons {n} (v : vl) (args: vec n vl) : fin (S n) → vl :=
    λ i,
      match i in fin (S n0) with
      | Fin.F1 => λ _, v
      | Fin.FS i' => λ args', args' i'
      end args.

  Definition emptyArgs : vec 0 vl := Fin.case0 _.
  Definition vhead {n} (args: vec (S n) vl) : vl := args Fin.F1.
  Definition vtail {n} (args: vec (S n) vl) : fin n → vl :=
    λ i, args (Fin.FS i).
End vec.

(* To prove saved_pred3_own_contractive, below, we need to hide n under ▶. *)
Definition mFun vl : oFunctor := { n & vec n vl -d> (var → vl) -d> vl -d> ▶ ∙ }.
Notation savedPred3G Σ vl := (savedAnythingG Σ (mFun vl)).
Notation savedPred3Σ vl := (savedAnythingΣ (mFun vl)).

Section saved_pred3.
  Import uPred EqNotations.

  (* For Iris. *)

  Global Instance projT1_ne {A P}: NonExpansive (projT1: @sigTO A P → leibnizO A).
  Proof. solve_proper. Qed.

  Lemma projT2_ne {A P}: ∀ n (x1 x2 : @sigTO A P) (Heq : x1 ≡{n}≡ x2),
    rew (sigT_dist_proj1 n Heq) in projT2 x1 ≡{n}≡ projT2 x2.
  Proof. by destruct Heq. Qed.

  Context `{!savedPred3G Σ vl}.

  Notation envD Σ := ((var → vl) -d> vl -d> iProp Σ).
  Notation hoEnvND n Σ := (vec n vl -d> envD Σ).

  Definition hoEnvD_P Σ := (λ n, hoEnvND n Σ).
  Definition hoEnvDO Σ : ofeT := sigTO (hoEnvD_P Σ).

  Definition packedFun : ofeT := mFun vl (iProp Σ) uPred_cofe.
  Definition packedFun_eq : packedFun =
    sigTO (λ n, vec n vl -d> (var → vl) -d> vl -d> laterO (iProp Σ)) := reflexivity _.

  Definition packedFun_arity : packedFun -n> natO := λne x, projT1 x.

  Implicit Types (Φ : hoEnvDO Σ) (Ψ : packedFun).

  (* Manipulate *)
  Definition close (Φ : hoEnvND 0 Σ): envD Σ := Φ emptyArgs.

  Definition beta {n} (Φ : hoEnvND (S n) Σ) (v : vl) : hoEnvND n Σ :=
    λ args, Φ (vcons v args).

  Definition lambda {n} (Φ : vl → hoEnvND n Σ) : hoEnvND (S n) Σ :=
    λ args, Φ (vhead args) (vtail args).

  Definition cpack n : hoEnvND n Σ → packedFun :=
    λ Φf, existT n (λ args ρ v, Next (Φf args ρ v)).

  Global Instance cpack_contractive: Contractive (cpack n).
  Proof.
    rewrite /cpack => ?????.
    apply (existT_ne _ eq_refl).
    solve_contractive_ho.
  Qed.
  Program Definition pack : hoEnvDO Σ -n> packedFun :=
    λne '(existT n Φ), cpack n Φ.
  Next Obligation.
    move => ?[??][??][/= Heq ?]. destruct Heq. by f_equiv.
  Qed.

  Definition saved_pred3_own (γ : gname) i (Φ : hoEnvND i Σ) : iProp Σ :=
    saved_anything_own (F := mFun vl) γ (pack (existT i Φ)).

  Instance saved_pred3_own_contractive γ i : Contractive (saved_pred3_own γ i).
  Proof.
    rewrite /saved_pred3_own => n f g /= Heq. f_equiv.
    apply (existT_ne _ eq_refl) => ??? /=.
    solve_contractive_ho.
  Qed.

  Lemma saved_pred3_alloc i (Φ : hoEnvND i Σ) :
    (|==> ∃ γ, saved_pred3_own γ i Φ)%I.
  Proof. apply saved_anything_alloc. Qed.

  Lemma eq_1 (Φ Ψ : packedFun) : Φ ≡ Ψ -∗
    ⌜ packedFun_arity Φ = packedFun_arity Ψ ⌝: iProp Σ.
  Proof.
    rewrite /= sigT_equivI /packedFun_arity.
    by iDestruct 1 as (Heq) "_".
  Qed.

  Lemma saved_pred3_agree_arity γ {i j α1 α2}:
    saved_pred3_own γ i α1 -∗ saved_pred3_own γ j α2 -∗
    ⌜ i = j ⌝.
  Proof.
    iIntros "HΦ1 HΦ2 /=".
    iDestruct (saved_anything_agree with "HΦ1 HΦ2") as "Heq".
    rewrite /= sigT_equivI /=. by iDestruct "Heq" as (Heq) "_".
  Qed.

  Lemma saved_pred3_agree γ i (Φ1 Φ2 : hoEnvND i Σ) a b c:
    saved_pred3_own γ i Φ1 -∗ saved_pred3_own γ i Φ2 -∗
    ▷ (Φ1 a b c ≡ Φ2 a b c).
  Proof.
    iIntros "HΦ1 HΦ2 /=".
    iDestruct (saved_anything_agree with "HΦ1 HΦ2") as "Heq".
    rewrite /= sigT_equivI. iDestruct "Heq" as (Heq) "Heq".
    rewrite (proof_irrel Heq eq_refl) /=.
    repeat setoid_rewrite bi.discrete_fun_equivI; iNext.
    iApply "Heq".
  Qed.

  Definition unpack :
    ∀ Ψ, hoEnvND (packedFun_arity Ψ) Σ :=
    λ '(existT n Φ), (λ args ρ v,
      let '(Next f) := (Φ args ρ v) in f)%I.

  Lemma same_arity {Φ Ψ : packedFun} {n} :
    Φ ≡{n}≡ Ψ → packedFun_arity Φ = packedFun_arity Ψ.
  Proof. destruct Φ, Ψ. by case. Qed.

  Lemma pred_impl (Φ Ψ : packedFun) n (Heq: Φ ≡{n}≡ Ψ)
    (a : vec (packedFun_arity Φ) vl) b c:
    Next (unpack Φ a b c) ≡{n}≡ Next (unpack Ψ (rew [λ n, vec n vl] (same_arity Heq) in a) b c).
  Proof.
    move: (same_arity Heq) => HeqN. destruct Φ, Ψ; simpl in *.
    case: Heq => /= Heq1.
    have {HeqN} ->: HeqN = Heq1. exact: proof_irrel.
    destruct Heq1; cbn => H. exact: H.
  Qed.

End saved_pred3.

Opaque saved_pred3_own.

Notation "γ ⤇ φ" := (saved_pred3_own γ φ) (at level 20).
