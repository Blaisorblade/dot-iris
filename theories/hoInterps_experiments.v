(* Must be loaded first, so that other modules can reset some flags. *)
Require Import Equations.Equations.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
From D Require Import iris_prelude saved_interp_n.
From D Require Import saved_interp_dep asubst_intf dlang.
From D.Dot Require syn operational unary_lr.
Import EqNotations.

Module try1.
Section saved_pred3_use.
  Context {vl : Type} {Σ : gFunctors}.

  Definition env := var → vl.
  Notation envD Σ := (env -d> vl -d> iProp Σ).
  Notation hoEnvD Σ := (list vl -d> envD Σ).
  Implicit Types (Φ : hoEnvD Σ) (n : nat).
  Definition eFalse : envD Σ := λ ρ v, False%I.

  (* We can track function arity by just storing a number,
     but that's a bit cumbersome. *)
  Definition hoEnvND Σ : Type := nat * hoEnvD Σ.
  Definition vcurry : hoEnvND Σ → vl → hoEnvND Σ := λ '(n, Φ) a,
    match n with
    | 0 => (0, λ _, eFalse)
    | S n => (n, λ args, Φ (a :: args))
    end%I.
  Definition vclose : hoEnvND Σ → envD Σ := λ '(n, Φ), Φ [].
  Definition vuncurry n (Φ : vl → hoEnvD Σ) : hoEnvND Σ :=
    (n + 1, λ args,
      match args with
      | w :: args => Φ w args
      | [] => eFalse
      end%I).
End saved_pred3_use.
End try1.

Module try2.
Module Type HoSemTypes (Import VS : VlSortsSig).
Include SavedInterpDep VS.

Notation savedHoSemTypeG Σ := (savedHoEnvPredG vl Σ).
Notation savedHoSemTypeΣ := (savedHoEnvPredΣ vl).

Section saved_ho_sem_type_extra.
  Context `{!savedHoSemTypeG Σ}.

  Implicit Types (Ψ : packedHoEnvD Σ).

  Definition packedHoEnvD_arity : packedHoEnvD Σ -n> natO := packedHoEnvPred_arity.

  Program Definition delay i {n}: hoD Σ n -n> hoD Σ n :=
    (λne φ, λ args v, ▷^i φ args v)%I.
  Next Obligation. move=>????? Heq ??. f_equiv. exact: Heq. Qed.

  Definition subtype {n} (φ1 φ2 : hoD Σ n) : iProp Σ :=
    (□∀ (args : vec vl n) v, ⌜ nclosed_vl v 0 ⌝ →
      φ1 args v -∗ φ2 args v)%I.
  Definition semEquiv {n} (φ1 φ2 : hoD Σ n) : iProp Σ :=
    (□∀ (args : vec vl n) v, ⌜ nclosed_vl v 0 ⌝ →
      φ1 args v ∗-∗ φ2 args v)%I.

  Fixpoint subtype_w_expKind ρ n :
      ∀ (φ1 φ2 : hoEnvD Σ n) (argTs : vec (envD Σ) n), iProp Σ :=
    match n with
    | 0 =>   λ φ1 φ2 argTs,
        ∀ v, vclose φ1 ρ v -∗ vclose φ2 ρ v
    | S n => λ φ1 φ2 argTs,
        ∀ v, vhead argTs ρ v -∗
          subtype_w_expKind ρ n (vcurry φ1 v) (vcurry φ2 v) (vtail argTs)
    end%I.

  Program Definition unNext: laterO (iProp Σ) -n> iProp Σ :=
    λne φ, (▷ later_car φ)%I.
  Next Obligation. solve_contractive. Qed.

  Definition unpack : ∀ Ψ, hoEnvD Σ (packedHoEnvD_arity Ψ) :=
    λ Ψ args ρ v, unNext (projT2 Ψ args ρ v).

  Lemma packedHoEnvD_arity_ne {Φ Ψ : packedHoEnvD Σ} {n} :
    Φ ≡{n}≡ Ψ → packedHoEnvD_arity Φ = packedHoEnvD_arity Ψ.
  Proof. apply packedHoEnvD_arity. Qed.

  Lemma unpack_ne {n Ψ1 Ψ2} (Heq : Ψ1 ≡{n}≡ Ψ2):
    rew [hoEnvD Σ] (packedHoEnvD_arity_ne Heq) in unpack Ψ1 ≡{n}≡ unpack Ψ2.
  Proof.
    move: Ψ1 Ψ2 Heq (packedHoEnvD_arity_ne Heq) => [/= n1 Φ1] [/= n2 Φ2] [/= Heq1 Heq] HeqN.
    move: Heq; rewrite (proof_irrel HeqN Heq1) /unpack /=.
    destruct Heq1 => /= H ???. f_contractive. exact: H.
  Qed.

  Lemma unpack_ne_eta n Ψ1 Ψ2 (Heq : Ψ1 ≡{n}≡ Ψ2) a b c:
    (rew [hoEnvD Σ] (packedHoEnvD_arity_ne Heq) in unpack Ψ1) a b c ≡{n}≡
    unpack Ψ2 a b c.
  Proof. exact: unpack_ne. Qed.
End saved_ho_sem_type_extra.
End HoSemTypes.

Import mapsto.

Import syn operational unary_lr.
Include HoSemTypes VlSorts.
Notation "s ↝n[ n ] φ" := (∃ γ, (s ↦ γ) ∗ (γ ⤇n[ n ] φ))%I  (at level 20) : bi_scope.

Section bar.
  Context `{!savedHoSemTypeG Σ} `{!dlangG Σ}.
  (* Implicit Types (interp : envD Σ) (φ : D). *)

  Definition dm_to_type (d : dm) n (φ : hoD Σ n) : iProp Σ :=
    (∃ s σ interp,
      s ↝n[ n ] interp ∗
      ⌜ d = dtysem σ s
       ∧ φ = λ args v, interp args (to_subst σ) v ⌝)%I.
  Global Arguments dm_to_type: simpl never.
  Notation "d ↗n[ n ] φ" := (dm_to_type d n φ) (at level 20).

  Definition skind Σ n := hoD Σ n -> iProp Σ.

  (* The point of Sandro's kind syntax is to use this only at kind 0. *)
  (* Definition sktmem {n} (φ1 φ2 : hoD Σ n) φ :=
    (subtype n 1 1 φ1 φ ∗ subtype n 1 1 φ φ)%I. *)
  Definition skintv (φ1 φ2 : hoD Σ 0) : skind Σ 0 := λ φ,
    (subtype φ1 φ ∗ subtype φ φ2)%I.
  (* Next Obligation.  move=>????? Heq. f_equiv. exact: Heq. solve_proper_ho. *)

  Definition skdelay {n} i (k : skind Σ n) : skind Σ n :=
    λ φ, k (delay i φ).
  Definition sktmem (φ1 φ2 : hoD Σ 0) : skind Σ 0 :=
    skdelay 1 (skintv (delay 1 φ1) (delay 1 φ2)).

  Definition skpi {n} (φ₁ : hoD Σ 0) (K : skind Σ n) : skind Σ (S n) :=
    λ φ, (□∀ arg, vclose φ₁ arg → K (vcurry φ arg))%I.

  (* Inductive kind : nat → Type :=
    | kintv : ty → ty → kind 0
    | kpi n : ty → kind n → kind (S n). *)

  Inductive kind : nat → Type :=
    | kintv : hoD Σ 0 → hoD Σ 0 → kind 0
    | kpi n : hoD Σ 0 → kind n → kind (S n).

  Fixpoint sem {n} (k : kind n) : skind Σ n :=
    match k with
      | kintv φ1 φ2 => skintv φ1 φ2
      | kpi n φ1 k' => skpi φ1 (sem k')
    end.

  Program Fixpoint sem_program {n} {struct n} : kind n → skind Σ n :=
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
  Equations sem_eq {n} : kind n → skind Σ n :=
    sem_eq (kintv φ1 φ2) := skintv φ1 φ2;
    sem_eq (kpi n φ1 k') := skpi φ1 (sem_eq k').

  Lemma unfold_sem_kintv φ1 φ2: sem_eq (kintv φ1 φ2) = skintv φ1 φ2.
  Proof. by simp sem_eq. Qed.

  Inductive hoSTy : nat → Type :=
    | TSWrap : hoEnvD Σ 0 → hoSTy 0
    | TSLam n : hoEnvD Σ 0 → hoSTy n → hoSTy (S n).
  Fixpoint hoSTySem {n} (T : hoSTy n): hoEnvD Σ n :=
    match T with
    | TSWrap φ => φ
    | TSLam n φ T' => vuncurry (λ v, hoSTySem T')
    end.

  Inductive htype : nat → Type :=
    | TWrap : ty → htype 0
    | TLam n : hoEnvD Σ 0 → htype n → htype (S n).

  Fixpoint typeSem {n} (T : htype n): hoEnvD Σ n :=
    (* match T in htype n0 return vec vl n0 -> env -> vl -> iProp Σ with *)
    match T in htype n0 return hoEnvD Σ n0 with
    (* match T return _ with *)
    | TWrap T' => vopen (⟦ T' ⟧ : envD Σ)
    | TLam n' φ T' =>
        (* XXX Now I need semantic substitution. *)
        (* vuncurry (A := envD Σ) (λ v, (typeSem T').|[v/]) *)
        (* Alternatives: *)
        vuncurry (A := envD Σ) (λ v args ρ, typeSem T' args (v .: ρ))
        (* λ args ρ, typeSem T' (vtail args) (vhead args .: ρ) *)
    end.

  Definition def_interp_tmem {n} : skind Σ n → envPred dm Σ :=
    λ K ρ d, (∃ φ, d.|[ρ] ↗n[ n ] φ ∗ K φ)%I.
  Definition def_interp_tmem_spec (φ1 φ2 : hoD Σ 0) : envPred dm Σ :=
    def_interp_tmem (sktmem φ1 φ2).

  (* Olty needed. Also, without using Olty, we can't use the fact that v is closed in a subtyping proof.
    *)
  (*
    A possible sketch of subtyping for lambdas? Not quite working...
    It's good, but we can't use to compare the various subtyping rules
    for lambdas. Also because my lambdas are total and work
    on arbitrary arguments — they might, at best, become False on bad
    ones. *)
  Definition lam_subtype {n} (argT : hoD Σ 0) (φ1 φ2 : hoD Σ (S n)) :=
    (□∀ arg, □ vclose argT arg -∗ subtype (vcurry φ1 arg) (vcurry φ2 arg))%I.

  Definition lam_semEquiv {n} (argT : hoD Σ 0) (φ1 φ2 : hoD Σ (S n)) :=
    (□∀ arg, □ vclose argT arg -∗ semEquiv (vcurry φ1 arg) (vcurry φ2 arg))%I.

  (* Here, we inherit eta from the metalanguage, in both directions. *)
  Lemma eta1 {n} argT (φ : hoD Σ (S n)): lam_subtype argT φ (λ v, φ v).
  Proof.
    rewrite /lam_subtype /subtype /vcurry /=.
    iIntros "!> * #Harg !> **". done.
  Qed.

  Lemma eta {n} argT (φ : hoD Σ (S n)): lam_semEquiv argT φ (λ v, φ v).
  Proof.
    rewrite /lam_semEquiv /semEquiv /vcurry /=.
    iIntros "!> * #Harg !> **"; rewrite -wand_iff_refl. done.
  Qed.
End bar.

Notation "d ↗n[ n ] φ" := (dm_to_type d n φ) (at level 20).
End try2.
