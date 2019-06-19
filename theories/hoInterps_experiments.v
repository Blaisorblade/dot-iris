From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
From D Require iris_prelude saved_interp_n.

Module try1.
Section saved_pred3_use.
  Context {vl : Type}.
  Import saved_interp_n.
  Context `{!savedPred3G Σ (var → vl) vl (list vl)}.
  Notation hoEnvD Σ := ((var → vl) -d> vl -d> (list vl) -d> iProp Σ).
  Implicit Type (Φ : hoEnvD Σ).
  Definition beta Φ a : hoEnvD Σ := λ ρ v args, Φ ρ v (a :: args).
  Definition close Φ := λ ρ v, Φ ρ v [].
  Definition lambda (Φ : vl → hoEnvD Σ) : hoEnvD Σ := λ ρ v args,
    match args with
    | w :: args => Φ w ρ v args
    | [] => False
    end%I.
End saved_pred3_use.
End try1.

Notation savedPred3G Σ A B C := (savedAnythingG Σ (A -d> B -d> C -d> ▶ ∙)).
Notation savedPred3Σ A B C := (savedAnythingΣ (A -d> B -d> C -d> ▶ ∙)).

Module try2.

Section saved_pred3.
  Definition vec n vl := fin n → vl.
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

  Context `{!savedPred3G Σ (var → vl) vl (list vl)}.

  Notation envD Σ := ((var → vl) -d> vl -d> iProp Σ).
  Notation hoEnvND n Σ := (vec n vl -d> envD Σ).
  (* Manipulate *)
  Definition close (Φ : hoEnvND 0 Σ): envD Σ := Φ emptyArgs.

  Definition beta {n} (Φ : hoEnvND (S n) Σ) (v : vl) : hoEnvND n Σ :=
    λ args, Φ (vcons v args).

  Definition lambda {n} (Φ : vl → hoEnvND n Σ) : hoEnvND (S n) Σ :=
    λ args, Φ (vhead args) (vtail args).

  Definition hoEnvD Σ := { n : nat & hoEnvND n Σ }.

  Context `{!savedPred3G Σ A B C}.
  Implicit Types (Φ : hoEnvD Σ).

  (* Argh. hoEnvD isn't a functor. *)
  (* Definition saved_pred3_own (γ : gname) Φ :=
    saved_anything_own
      (F := A -d> B -d> C -d> ▶ ∙) γ (λ a b c, Next (Φ a b c)). *)
(*
  Instance saved_pred3_own_contractive γ : Contractive (saved_pred3_own γ).
  Proof. rewrite /saved_pred3_own /saved_anything_own. solve_contractive_ho. Qed.

  Lemma saved_pred3_alloc Φ :
    (|==> ∃ γ, saved_pred3_own γ Φ)%I.
  Proof. apply saved_anything_alloc. Qed.

  Lemma saved_pred3_agree γ Φ Ψ a b c:
    saved_pred3_own γ Φ -∗ saved_pred3_own γ Ψ -∗
    ▷ (Φ a b c ≡ Ψ a b c).
  Proof.
    iIntros "HΦ HΨ /=".
    iDestruct (saved_anything_agree with "HΦ HΨ") as "Heq".
    repeat setoid_rewrite bi.discrete_fun_equivI.
    iApply bi.later_equivI; iApply "Heq".
  Qed. *)
End saved_pred3.

(*
Opaque saved_pred3_own.

Notation "γ ⤇ φ" := (saved_pred3_own γ φ) (at level 20).
*)
