From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
From D Require Import prelude iris_prelude saved_interp_n.
From D Require Import saved_interp_dep.
Import uPred EqNotations.

Module try1.
Section saved_pred3_use.
  Context {vl : Type} {Σ : gFunctors}.

  Notation _envD Σ := ((var → vl) -d> vl -d> iProp Σ).
  Notation hoEnvD Σ := (list vl -d> _envD Σ).
  Implicit Types (Φ : hoEnvD Σ) (n : nat).
  Definition eFalse : _envD Σ := λ ρ v, False%I.

  (* We can track function arity by just storing a number,
     but that's a bit cumbersome. *)
  Definition hoEnvND Σ : Type := nat * hoEnvD Σ.
  Definition beta : hoEnvND Σ → vl → hoEnvND Σ := λ '(n, Φ) a,
    match n with
    | 0 => (0, λ _, eFalse)
    | S n => (n, λ args, Φ (a :: args))
    end%I.
  Definition close : hoEnvND Σ → _envD Σ := λ '(n, Φ), Φ [].
  Definition lambda n (Φ : vl → hoEnvD Σ) : hoEnvND Σ :=
    (n + 1, λ args,
      match args with
      | w :: args => Φ w args
      | [] => eFalse
      end%I).
End saved_pred3_use.
End try1.

Module try2.
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

  (* Manipulation of higher-order semantic types. *)
  Definition close {A} (Φ : vec 0 vl -d> A): A := Φ emptyArgs.

  Definition beta {n A} (Φ : vec (S n) vl -d> A) v : vec n vl -d> A :=
    λ args, Φ (vcons v args).

  Definition lambda {n A} (Φ : vl → vec n vl -d> A) :
    vec (S n) vl -d> A :=
    λ args, Φ (vhead args) (vtail args).
End vec.

From D Require Import asubst_intf dlang olty.

Module HoSemTypes (values: Values) (sorts: SortsIntf values).

(* Module M := (OLty values sorts). Import M. *)
Import values sorts.

Notation _envD Σ := ((var → vl) -d> vl -d> iProp Σ).
Notation hoEnvND n Σ := (vec n vl -d> _envD Σ).
Definition hoD n Σ := vec n vl -d> vl -d> iProp Σ.

Section saved_ho_sem_type_extra.
  Context `{!savedHoSemTypeG vl Σ}.

  Implicit Types (Ψ : packedFun vl Σ).

  Definition subtype {n} i j (φ1 φ2 : hoD n Σ) : iProp Σ :=
    (□∀ (args : vec n vl) v, ⌜ nclosed_vl v 0 ⌝ →
      ▷^i φ1 args v -∗ ▷^j φ2 args v)%I.
  Definition semEquiv {n} i j (φ1 φ2 : hoD n Σ) : iProp Σ :=
    (□∀ (args : vec n vl) v, ⌜ nclosed_vl v 0 ⌝ → ▷^i φ1 args v ∗-∗ ▷^j φ2 args v)%I.

  Fixpoint subtype_w_expKind ρ n :
      ∀ (φ1 φ2 : hoEnvND n Σ) (argTs : vec n (_envD Σ)), iProp Σ :=
    match n with
    | 0 =>   λ φ1 φ2 argTs,
        ∀ v, close φ1 ρ v -∗ close φ2 ρ v
    | S n => λ φ1 φ2 argTs,
        ∀ v, vhead argTs ρ v -∗
          subtype_w_expKind ρ n (beta φ1 v) (beta φ2 v) (vtail argTs)
    end%I.

  Lemma packedFun_arity_ne {Φ Ψ : packedFun vl Σ} {n} :
    Φ ≡{n}≡ Ψ → packedFun_arity Φ = packedFun_arity Ψ.
  Proof. apply packedFun_arity. Qed.

  Program Definition unNext: laterO (iProp Σ) -n> iProp Σ :=
    λne φ, (▷ later_car φ)%I.
  Next Obligation. solve_contractive. Qed.

  Definition unpack : ∀ Ψ, hoEnvND (packedFun_arity Ψ) Σ :=
    λ Ψ args ρ v, unNext (projT2 Ψ args ρ v).

  Lemma unpack_ne {n Ψ1 Ψ2} (Heq : Ψ1 ≡{n}≡ Ψ2):
    rew [hoEnvD_P vl Σ] (packedFun_arity_ne Heq) in unpack Ψ1 ≡{n}≡ unpack Ψ2.
  Proof.
    move: Ψ1 Ψ2 Heq (packedFun_arity_ne Heq) => [/= n1 Φ1] [/= n2 Φ2] [/= Heq1 Heq] HeqN.
    move: Heq; rewrite (proof_irrel HeqN Heq1) /unpack /=.
    destruct Heq1 => /= H ???. f_contractive. exact: H.
  Qed.

  Lemma unpack_ne_eta n Ψ1 Ψ2 (Heq : Ψ1 ≡{n}≡ Ψ2) a b c:
    (rew [hoEnvD_P vl Σ] (packedFun_arity_ne Heq) in unpack Ψ1) a b c ≡{n}≡
    unpack Ψ2 a b c.
  Proof. exact: unpack_ne. Qed.
End saved_ho_sem_type_extra.
End HoSemTypes.

Notation "s ↝[ n ] φ" := (∃ γ, (s ↦ γ) ∗ (γ ⤇[ n ] φ))%I  (at level 20) : bi_scope.

From D.Dot Require Import syn operational.
Include HoSemTypes syn syn.

Section bar.
  Context `{!savedHoSemTypeG vl Σ} `{!dlangG Σ}.
  (* Implicit Types (interp : _envD Σ) (φ : D). *)

  Definition idm_proj_semtype (d : dm) n (φ : hoD n Σ) : iProp Σ :=
    (∃ s σ interp,
      s ↝[ n ] interp ∗
      ⌜ d = dtysem σ s
       ∧ φ = λ args v, interp args (to_subst σ) v ⌝)%I.
  Global Arguments idm_proj_semtype: simpl never.
  Notation "d ↗[ n ] φ" := (idm_proj_semtype d n φ) (at level 20).

  Notation envPred s := (vls -d> s -d> iProp Σ).


  Definition kind n Σ := hoD n Σ → iProp Σ.

  (* The point of Sandro's kind syntax is to use this only at kind 0. *)
  (* Definition ktmem {n} (φ1 φ2 : hoD n Σ) φ :=
    (subtype n 1 1 φ1 φ ∗ subtype n 1 1 φ φ)%I. *)
  Definition ktmem (φ1 φ2 : hoD 0 Σ) φ :=
    (subtype 1 1 φ1 φ ∗ subtype 1 1 φ φ)%I.

  Definition kpi {n} (K : kind n Σ) (φ₁ : hoD 0 Σ) : kind (S n) Σ :=
    λ φ, (□∀ arg, close φ₁ arg → K (beta φ arg))%I.

  Definition def_interp_tmem {n} : kind n Σ → envPred dm :=
    λ K ρ d, (∃ φ, d ↗[ n ] φ ∗ K φ)%I.
  Definition def_interp_tmem_spec (φ1 φ2 : hoD 0 Σ) : envPred dm :=
    def_interp_tmem (ktmem φ1 φ2).
  (* Olty needed. Also, without using Olty, we can't use the fact that v is closed in a subtyping proof.
    *)
  (*
    A possible sketch of subtyping for lambdas? Not quite working...
    It's good, but we can't use to compare the various subtyping rules
    for lambdas. Also because my lambdas are total and work
    on arbitrary arguments — they might, at best, become False on bad
    ones. *)
  Definition lam_subtype {n} (argT : hoD 0 Σ) (φ1 φ2 : hoD (S n) Σ) :=
    (□∀ arg, □close argT arg -∗ subtype 0 0 (beta φ1 arg) (beta φ2 arg))%I.

  Definition lam_semEquiv {n} (argT : hoD 0 Σ) (φ1 φ2 : hoD (S n) Σ) :=
    (□∀ arg, □close argT arg -∗ semEquiv 0 0 (beta φ1 arg) (beta φ2 arg))%I.

  (* Here, we inherit eta from the metalanguage, in both directions. *)
  Lemma eta1 {n} argT (φ : hoD (S n) Σ): lam_subtype argT φ (λ v, φ v).
  Proof.
    rewrite /lam_subtype /subtype /beta /=.
    iIntros "!>" (arg) "#Harg !>"; iIntros (args v Hcl) "? //".
  Qed.

  Lemma eta {n} argT (φ : hoD (S n) Σ): lam_semEquiv argT φ (λ v, φ v).
  Proof.
    rewrite /lam_semEquiv /semEquiv /beta /=.
    iIntros "!>" (arg) "#Harg !>"; iIntros (args v Hcl).
    by iApply wand_iff_refl.
  Qed.
End bar.

Notation "d ↗[ n ] φ" := (idm_proj_semtype d n φ) (at level 20).
