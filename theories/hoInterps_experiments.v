(* Must be loaded first, so that other modules can reset some flags. *)
Require Import Equations.Equations.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
From D Require Import iris_prelude saved_interp_n.
From D Require Import saved_interp_dep asubst_intf dlang.
Import EqNotations mapsto.
From D.Dot Require Import syn operational unary_lr.

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
  Definition tCurry : hoEnvND Σ → vl → hoEnvND Σ := λ '(n, Φ) a,
    match n with
    | 0 => (0, λ _, eFalse)
    | S n => (n, λ args, Φ (a :: args))
    end%I.
  Definition close : hoEnvND Σ → _envD Σ := λ '(n, Φ), Φ [].
  Definition tUncurry n (Φ : vl → hoEnvD Σ) : hoEnvND Σ :=
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

  Definition tCurry {n A} (Φ : vec (S n) vl -d> A) : vl -d> vec n vl -d> A :=
    λ v args, Φ (vcons v args).

  Definition tUncurry {n A} (Φ : vl → vec n vl -d> A) :
    vec (S n) vl -d> A :=
    λ args, Φ (vhead args) (vtail args).
End vec.

Module HoSemTypes (Import sorts: SortsIntf).
(* Module M := (OLty values). Import M. *)
(* Notation _envD vl Σ := ((var → vl) -d> vl -d> iProp Σ).
Notation hoEnvND n vl Σ := (vec n vl -d> _envD vl Σ). *)

(* Forwarding. *)
Notation _envD Σ := (pred (var → vl) vl Σ).
Notation hoEnvND n Σ := (hoPredN n vl (var → vl) vl Σ).
Definition hoD n Σ := vec n vl -d> vl -d> iProp Σ.

Definition hoEnvD_P2 Σ := (λ n, hoEnvND n Σ).
Definition hoEnvDO2 Σ : ofeT := sigTO (hoEnvD_P2 Σ).
Definition hoEnvDOF2 : oFunctor := { n & vec n vl -d> (var → vl) -d> vl -d> ▶ ∙ }.
Notation savedHoSemTypeG2 Σ := (savedAnythingG Σ (hoEnvDOF2 vl)).
Notation savedHoSemTypeΣ2 := (savedAnythingΣ (hoEnvDOF2 vl)).

Definition hoEnvD_P Σ := hoPred_P vl (var → vl) vl Σ.
Definition hoEnvDO Σ : ofeT := hoPredO vl (var → vl) vl Σ.
Definition hoEnvDOF : oFunctor := hoPredOF vl (var → vl) vl.

Notation savedHoSemTypeG Σ := (savedHoPredG vl (var → vl) vl Σ).
Notation savedHoSemTypeΣ := (savedHoPredΣ vl (var → vl) vl).

(* Shadowing. *)
Definition packedHoEnvD Σ := packedHoPred vl (var → vl) vl Σ.

Section saved_ho_sem_type_extra.
  Context `{!savedHoSemTypeG Σ}.

  Implicit Types (Ψ : packedHoEnvD Σ).

  Definition packedHoEnvD_arity : packedHoEnvD Σ -n> natO := packedHoPred_arity.

  Program Definition delay i {n}: hoD n Σ -n> hoD n Σ :=
    (λne φ, λ args v, ▷^i φ args v)%I.
  Next Obligation. move=>????? Heq ??. f_equiv. exact: Heq. Qed.

  Definition subtype {n} (φ1 φ2 : hoD n Σ) : iProp Σ :=
    (□∀ (args : vec n vl) v, ⌜ nclosed_vl v 0 ⌝ →
      φ1 args v -∗ φ2 args v)%I.
  Definition semEquiv {n} (φ1 φ2 : hoD n Σ) : iProp Σ :=
    (□∀ (args : vec n vl) v, ⌜ nclosed_vl v 0 ⌝ →
      φ1 args v ∗-∗ φ2 args v)%I.

  Fixpoint subtype_w_expKind ρ n :
      ∀ (φ1 φ2 : hoEnvND n Σ) (argTs : vec n (_envD Σ)), iProp Σ :=
    match n with
    | 0 =>   λ φ1 φ2 argTs,
        ∀ v, close φ1 ρ v -∗ close φ2 ρ v
    | S n => λ φ1 φ2 argTs,
        ∀ v, vhead argTs ρ v -∗
          subtype_w_expKind ρ n (tCurry φ1 v) (tCurry φ2 v) (vtail argTs)
    end%I.

  Program Definition unNext: laterO (iProp Σ) -n> iProp Σ :=
    λne φ, (▷ later_car φ)%I.
  Next Obligation. solve_contractive. Qed.

  Definition unpack : ∀ Ψ, hoEnvND (packedHoEnvD_arity Ψ) Σ :=
    λ Ψ args ρ v, unNext (projT2 Ψ args ρ v).

  Lemma packedHoEnvD_arity_ne {Φ Ψ : packedHoEnvD Σ} {n} :
    Φ ≡{n}≡ Ψ → packedHoEnvD_arity Φ = packedHoEnvD_arity Ψ.
  Proof. apply packedHoEnvD_arity. Qed.

  Lemma unpack_ne {n Ψ1 Ψ2} (Heq : Ψ1 ≡{n}≡ Ψ2):
    rew [hoEnvD_P Σ] (packedHoEnvD_arity_ne Heq) in unpack Ψ1 ≡{n}≡ unpack Ψ2.
  Proof.
    move: Ψ1 Ψ2 Heq (packedHoEnvD_arity_ne Heq) => [/= n1 Φ1] [/= n2 Φ2] [/= Heq1 Heq] HeqN.
    move: Heq; rewrite (proof_irrel HeqN Heq1) /unpack /=.
    destruct Heq1 => /= H ???. f_contractive. exact: H.
  Qed.

  Lemma unpack_ne_eta n Ψ1 Ψ2 (Heq : Ψ1 ≡{n}≡ Ψ2) a b c:
    (rew [hoEnvD_P Σ] (packedHoEnvD_arity_ne Heq) in unpack Ψ1) a b c ≡{n}≡
    unpack Ψ2 a b c.
  Proof. exact: unpack_ne. Qed.
End saved_ho_sem_type_extra.
End HoSemTypes.

Import mapsto.
Notation "s ↝[ n ] φ" := (∃ γ, (s ↦ γ) ∗ (γ ⤇[ n ] φ))%I  (at level 20) : bi_scope.

Include HoSemTypes syn.

Section bar.
  Context `{!savedHoSemTypeG Σ} `{!dlangG Σ}.
  (* Implicit Types (interp : _envD Σ) (φ : D). *)

  Definition idm_proj_semtype (d : dm) n (φ : hoD n Σ) : iProp Σ :=
    (∃ s σ interp,
      s ↝[ n ] interp ∗
      ⌜ d = dtysem σ s
       ∧ φ = λ args v, interp args (to_subst σ) v ⌝)%I.
  Global Arguments idm_proj_semtype: simpl never.
  Notation "d ↗[ n ] φ" := (idm_proj_semtype d n φ) (at level 20).

  Notation envPred s := ((var → vl) -d> s -d> iProp Σ).

  Definition skind n Σ := hoD n Σ -> iProp Σ.

  (* The point of Sandro's kind syntax is to use this only at kind 0. *)
  (* Definition sktmem {n} (φ1 φ2 : hoD n Σ) φ :=
    (subtype n 1 1 φ1 φ ∗ subtype n 1 1 φ φ)%I. *)
  Definition skintv (φ1 φ2 : hoD 0 Σ) : skind 0 Σ := λ φ,
    (subtype φ1 φ ∗ subtype φ φ2)%I.
  (* Next Obligation.  move=>????? Heq. f_equiv. exact: Heq. solve_proper_ho. *)

  Definition skdelay {n} i (k : skind n Σ) : skind n Σ :=
    λ φ, k (delay i φ).
  Definition sktmem (φ1 φ2 : hoD 0 Σ) : skind 0 Σ :=
    skdelay 1 (skintv (delay 1 φ1) (delay 1 φ2)).

  Definition skpi {n} (φ₁ : hoD 0 Σ) (K : skind n Σ) : skind (S n) Σ :=
    λ φ, (□∀ arg, close φ₁ arg → K (tCurry φ arg))%I.

  (* Inductive kind : nat → Type :=
    | kintv : ty → ty → kind 0
    | kpi n : ty → kind n → kind (S n). *)

  Inductive kind : nat → Type :=
    | kintv : hoD 0 Σ → hoD 0 Σ → kind 0
    | kpi n : hoD 0 Σ → kind n → kind (S n).

  Fixpoint sem {n} (k : kind n) : skind n Σ :=
    match k with
      | kintv φ1 φ2 => skintv φ1 φ2
      | kpi n φ1 k' => skpi φ1 (sem k')
    end.

  Program Fixpoint sem_program {n} {struct n} : kind n → skind n Σ :=
    match n return _ with
    | 0 => λ k, match k with
      | kintv φ1 φ2 => skintv φ1 φ2
      | kpi n _ _ => _
      end
    | S n => λ k, match k with
      | kintv φ1 φ2 => _
      | kpi n φ1 k' =>
        skpi φ1 (sem_program (rew _ in k'))
      end
    end.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. intros; congruence. Defined.
  (* Derive Signature NoConfusion Subterm EqDec for kind. *)

  Derive Signature for kind.
  Equations sem_eq {n} : kind n → skind n Σ :=
    sem_eq (kintv φ1 φ2) := skintv φ1 φ2;
    sem_eq (kpi n φ1 k') := skpi φ1 (sem_eq k').

  Lemma unfold_sem_kintv φ1 φ2: sem_eq (kintv φ1 φ2) = skintv φ1 φ2.
  Proof. by simp sem_eq. Qed.

  Inductive hoSTy : nat → Type :=
    | TSWrap : hoEnvND 0 Σ → hoSTy 0
    | TSLam n : hoEnvND 0 Σ → hoSTy n → hoSTy (S n).
  Fixpoint hoSTySem {n} (T : hoSTy n): hoEnvND n Σ :=
    match T with
    | TSWrap φ => φ
    | TSLam n φ T' => tUncurry (λ v, hoSTySem T')
    end.

  Inductive htype : nat → Type :=
    | TWrap : nat → ty → htype 0
    | TLam n : hoEnvND 0 Σ → htype n → htype (S n).
  (* Now I need substitution. *)

  (** This takes the first [n] elements from ρ *)
  Definition to_subst_inv (n : nat) (ρ : var → vl) : vls :=
    map ρ (seq 0 n).

  Lemma to_subst_inv_spec ρ : to_subst_inv (length ρ) (to_subst ρ) = ρ.
  Proof.
    rewrite /to_subst_inv; elim: ρ => /= [//|v ρ IH].
    rewrite /= -seq_shift; f_equal. by rewrite map_map.
  Qed.

  Program Fixpoint typeSem {n} (T : htype n): hoEnvND n Σ :=
    match T with
    | TWrap n T' => λ _ ρ, ⟦ T' ⟧ (to_subst_inv n ρ)
    | TLam n φ T' => tUncurry (λ v, typeSem T')
    end.

 (* move => _ n _ k ? φ1 k' [?] ?. //. subst.
  refine (res). Defined. *)

  Definition def_interp_tmem {n} : skind n Σ → envPred dm :=
    λ K ρ d, (∃ φ, d.|[ρ] ↗[ n ] φ ∗ K φ)%I.
  Definition def_interp_tmem_spec (φ1 φ2 : hoD 0 Σ) : envPred dm :=
    def_interp_tmem (sktmem φ1 φ2).

  (* Olty needed. Also, without using Olty, we can't use the fact that v is closed in a subtyping proof.
    *)
  (*
    A possible sketch of subtyping for lambdas? Not quite working...
    It's good, but we can't use to compare the various subtyping rules
    for lambdas. Also because my lambdas are total and work
    on arbitrary arguments — they might, at best, become False on bad
    ones. *)
  Definition lam_subtype {n} (argT : hoD 0 Σ) (φ1 φ2 : hoD (S n) Σ) :=
    (□∀ arg, □close argT arg -∗ subtype (tCurry φ1 arg) (tCurry φ2 arg))%I.

  Definition lam_semEquiv {n} (argT : hoD 0 Σ) (φ1 φ2 : hoD (S n) Σ) :=
    (□∀ arg, □close argT arg -∗ semEquiv (tCurry φ1 arg) (tCurry φ2 arg))%I.

  (* Here, we inherit eta from the metalanguage, in both directions. *)
  Lemma eta1 {n} argT (φ : hoD (S n) Σ): lam_subtype argT φ (λ v, φ v).
  Proof.
    rewrite /lam_subtype /subtype /tCurry /=.
    iIntros "!> * #Harg !> **". done.
  Qed.

  Lemma eta {n} argT (φ : hoD (S n) Σ): lam_semEquiv argT φ (λ v, φ v).
  Proof.
    rewrite /lam_semEquiv /semEquiv /tCurry /=.
    iIntros "!> * #Harg !> **"; rewrite -wand_iff_refl. done.
  Qed.
End bar.

Notation "d ↗[ n ] φ" := (idm_proj_semtype d n φ) (at level 20).
End try2.
