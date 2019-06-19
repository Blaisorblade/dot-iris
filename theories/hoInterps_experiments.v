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

(* To prove saved_pred3_own_contractive, below, we need to hide n under ▶. *)
Definition nFun vl : oFunctor := { n & vec n vl -d> (var → vl) -d> vl -d> ∙ }.
Definition mFun vl : oFunctor := ▶ nFun vl.
Notation savedPred3G Σ vl := (savedAnythingG Σ (mFun vl)).
Notation savedPred3Σ vl := (savedAnythingΣ (mFun vl)).

Section saved_pred3.
  Context `{!savedPred3G Σ vl}.

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

  Notation envD Σ := ((var → vl) -d> vl -d> iProp Σ).
  Notation hoEnvND n Σ := (vec n vl -d> envD Σ).
  (* Manipulate *)
  Definition close (Φ : hoEnvND 0 Σ): envD Σ := Φ emptyArgs.

  Definition beta {n} (Φ : hoEnvND (S n) Σ) (v : vl) : hoEnvND n Σ :=
    λ args, Φ (vcons v args).

  Definition lambda {n} (Φ : vl → hoEnvND n Σ) : hoEnvND (S n) Σ :=
    λ args, Φ (vhead args) (vtail args).

  Definition hoEnvD Σ := { n : nat & hoEnvND n Σ }.

  (* Make hoEnvD a Cofe. *)
  Definition hoEnvDC Σ : ofeT := sigTC (λ n, hoEnvND n Σ).
  Global Instance: Cofe (hoEnvDC Σ) := _.

  Implicit Types (Φ : hoEnvD Σ).

  Definition packedFun := nFun vl (iProp Σ) uPred_cofe.
  Definition pack : hoEnvD Σ → laterO packedFun :=
    λ '(existT n Φ), Next (existT n (λ args ρ v, Φ args ρ v)).

  Definition packedFun_arity : packedFun → nat := projT1.
  Definition unpack : ∀ (Φ : packedFun), hoEnvND (packedFun_arity Φ) Σ := projT2.

  Definition saved_pred3_own (γ : gname) (Φ : hoEnvD Σ) : iProp Σ :=
    saved_anything_own (F := mFun vl) γ (pack Φ).

  Instance saved_pred3_own_contractive γ : Contractive (saved_pred3_own γ).
  Proof. rewrite /saved_pred3_own => n [ix x] [iy y] /= Heq. f_equiv. done. Qed.

  Import uPred EqNotations.
  Instance: NonExpansive (projT1 : packedFun → nat). solve_proper. Qed.

  Lemma saved_pred3_alloc Φ :
    (|==> ∃ γ, saved_pred3_own γ Φ)%I.
  Proof. apply saved_anything_alloc. Qed.

  Lemma saved_pred3_agree γ Φ Ψ:
    saved_pred3_own γ Φ -∗ saved_pred3_own γ Ψ -∗
    ▷ (Φ ≡ Ψ).
  Proof.
    iIntros "HΦ HΨ /=".
    iDestruct (saved_anything_agree with "HΦ HΨ") as "Heq".
    destruct Φ, Ψ; rewrite /pack.
    iApply bi.later_equivI; iApply "Heq".
  Qed.

  Lemma same_arity {Φ Ψ : packedFun} {n} :
    Φ ≡{n}≡ Ψ → packedFun_arity Φ = packedFun_arity Ψ.
  Proof. destruct Φ, Ψ. by case. Qed.

  Lemma eq_ext (Φ Ψ : packedFun) : Φ ≡ Ψ ⊢ ⌜ ∃ n, Φ ≡{n}≡ Ψ ⌝: iProp Σ.
  Proof. unseal; constructor => n x Hx /=. by exists n. Qed.

  Lemma pred_impl (Φ Ψ : packedFun) n (Heq: Φ ≡{n}≡ Ψ)
    (a : vec (packedFun_arity Φ) vl) b c:
    unpack Φ a b c ≡{n}≡ unpack Ψ (rew [λ n, vec n vl] (same_arity Heq) in a) b c.
  Proof.
    move: (same_arity Heq) => HeqN. destruct Φ, Ψ; simpl in *.
    case: Heq => /= Heq1.
    have {HeqN} ->: HeqN = Heq1. exact: proof_irrel.
    destruct Heq1; cbn => H. exact: H.
  Qed.

  Lemma eq_1 (Φ Ψ : packedFun) : Φ ≡ Ψ -∗ ⌜ packedFun_arity Φ = packedFun_arity Ψ ⌝: iProp Σ.
  Proof.
    iIntros "H".
    iApply (internal_eq_rewrite _ _ (λ x, ⌜ packedFun_arity Φ = packedFun_arity x ⌝)%I with "H") => //.
    move => n [/= ix ?] [/= iy ?] [/=]. intros ->. done.
  Qed.

  Lemma saved_pred3_agree_arity γ Φ Ψ:
    saved_pred3_own γ Φ -∗ saved_pred3_own γ Ψ -∗
    ▷ ⌜ packedFun_arity Φ = packedFun_arity Ψ ⌝.
  Proof.
    iIntros "HΦ HΨ /=".
    iDestruct (saved_pred3_agree with "HΦ HΨ") as "Heq".
    iNext. iApply (eq_1 with "Heq").
  Qed.
(*
  Lemma saved_pred3_agree γ Φ Ψ a b c:
    saved_pred3_own γ Φ -∗ saved_pred3_own γ Ψ -∗
    ⌜ proj1_sig Φ ⌝
    ▷ (Φ a b c ≡ Ψ a b c).
  Proof.
    iIntros "HΦ HΨ /=".
    iDestruct (saved_anything_agree with "HΦ HΨ") as "Heq".
    repeat setoid_rewrite bi.discrete_fun_equivI.
    iApply bi.later_equivI; iApply "Heq".
  Qed. *)

End saved_pred3.

Opaque saved_pred3_own.

Notation "γ ⤇ φ" := (saved_pred3_own γ φ) (at level 20).
