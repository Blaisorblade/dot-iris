(* (* Must be loaded first, so that other modules can reset some flags. *)
Require Import Equations.Equations. *)
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
From D Require Import iris_prelude saved_interp_n.
From D Require Import saved_interp_dep asubst_intf dlang ty_interp_subst_lemmas.
From Coq Require FunctionalExtensionality.
From D Require swap_later_impl.
Import EqNotations.

Set Suggest Proof Using.
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Strict Implicit.

Module try1 (Import VS : VlSortsSig).
Section saved_pred3_use.
  Context {Σ : gFunctors}.

  Notation envD Σ := (env -d> vl -d> iPropO Σ).
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
    (S n, λ args,
      match args with
      | w :: args => Φ w args
      | [] => eFalse
      end%I).
End saved_pred3_use.
End try1.
From D Require Import saved_interp_dep lty asubst_base.

Module noDepTypes.
Module Type HoSemTypes (Import VS : VlSortsFullSig) (Import LWP : LiftWp VS).
Include Lty VS LWP.
Section saved_dep_use.
  Context {Σ : gFunctors}.
  Notation hoEnvND Σ := (sigTO (hoEnvD Σ)).
  Implicit Types (Φ : hoEnvND Σ) (n : nat).
  Definition eFalse : envD Σ := λ ρ v, False%I.

  Unset Program Cases.
  Program Definition vcurry : hoEnvND Σ → vl → hoEnvND Σ := λ '(existT n φ),
    match n with
    | 0 => λ _ _, existT 0 (λ _, eFalse)
    | S m => λ φ a, existT m (λ args : vec vl m, φ (vcons a args))
    end φ.

  Definition vclose : hoEnvND Σ → envD Σ := λ '(existT n φ),
    match n with
    | 0 => λ φ, φ vnil
    | S n => λ _, eFalse
    end φ.
  Lemma vclose_id φ : vclose (existT 0 φ) = φ vnil. Proof. done. Qed.

  Program Definition vuncurry' : {n & vl → hoEnvD Σ n} → hoEnvND Σ := λ '(existT n φ),
    existT (S n) (λ args, φ (vhead args) (vtail args)).
  Program Definition vuncurry n : (vl → hoEnvND Σ) → hoEnvND Σ := λ φ,
    existT (S n) (λ args,
      let '(existT m φ') := φ (vhead args) in
      match decide (m = n) with
      | left Heq => φ' (rew <- [vec vl] Heq in vtail args)
      | right _ => eFalse
      end).
  Lemma vec_eta {A n} (args : vec A (S n)) : vcons (vhead args) (vtail args) = args.
  Proof. by dependent destruction args. Qed.

  Lemma vcurry_vuncurry n (φ : hoEnvD Σ (S n)) : vuncurry n (vcurry (existT (S n) φ)) = existT (S n) φ.
  Proof.
    rewrite /vuncurry; cbn; destruct n; f_equiv;
      apply FunctionalExtensionality.functional_extensionality_dep => args;
      by rewrite (decide_left (P := (_ = _)) eq_refl) vec_eta.
  Qed.

  Lemma vuncurry_vcurry n (φ : vl → hoEnvD Σ n) :
    vcurry (vuncurry n (λ v, existT n (φ v))) = (λ v, existT n (φ v)).
  Proof.
    apply FunctionalExtensionality.functional_extensionality_dep => v.
    cbn; f_equiv.
    apply FunctionalExtensionality.functional_extensionality_dep => args /=.
    by rewrite (decide_left (P := (_ = _)) eq_refl).
  Qed.
End saved_dep_use.
End HoSemTypes.
End noDepTypes.

From D Require Import hoInterps_experiments.

(** The semantics of a kind includes a predicate on types, and a subtype predicate.
  *)
(* XXX make these non-expansive? *)
Module Type HoSemTypes2 (Import VS : VlSortsFullSig) (Import LWP : LiftWp VS) (Import L : Lty VS LWP).
Include HoSemTypes VS LWP L.


Section saved_ho_sem_type_extra.
  Context {Σ : gFunctors}.

  Implicit Types (Ψ : packedHoEnvD Σ).

  (** ** Accessing saved HO predicates. *)
  Definition packedHoEnvD_arity : packedHoEnvD Σ -n> natO := packedHoEnvPred_arity.

  Program Definition unNext: laterO (iPropO Σ) -n> iPropO Σ :=
    λne φ, (▷ later_car φ)%I.
  Next Obligation. solve_contractive. Qed.

  Definition unpack : ∀ Ψ, hoEnvD Σ (packedHoEnvD_arity Ψ) :=
    λ Ψ args ρ v, unNext (projT2 Ψ args ρ v).
  Arguments unpack : clear implicits.

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


(* :: is at level 60. *)
(* Notation "Γ s⊨k T1 , i <: T2 , j ∷ K" := (sstpk i j Γ T1 T2 K)
  (at level 74, i, j at level 59, T1, T2, i at next level). *)

(* XXX Should we delay [T] as well? Yes, based on [iSel_Sub]/[iSub_Sel].
Should we delay K?*)
(* V1: delay K and rely on swaps to make that affect all types. This is needed somewhere. *)
(* Definition sktp `{dlangG Σ} {n} i Γ T (K : sf_kind Σ n) : iProp Σ :=
  □∀ ρ, s⟦Γ⟧*ρ → ▷^i K ρ T. *)
(* V2: push the delay down. *)
(* Definition sktp `{dlangG Σ} {n} i Γ T (K : sf_kind Σ n) : iProp Σ :=
  □∀ ρ, s⟦Γ⟧*ρ → ▷^i K ρ (envApply (oLaterN i T) ρ). *)
(* XXX What delays are wanted here? *)
(* Definition ssktp `{dlangG Σ} {n} i Γ (K1 K2 : sf_kind Σ n) : iProp Σ :=
  □∀ ρ T, s⟦Γ⟧*ρ → ▷^i K1 ρ (envApply T ρ) → ▷^i K2 ρ (envApply T ρ). *)

End HoSemTypes2.

(* Instance: Persistent (subtype_lty (Σ := Σ) a b) := _. *)
(* Instance: Persistent (a ⊂@{lty Σ} b). *)
(* Class ISubsetEq
Print ltyO. *)

(* Instance SubsetEq_lty {Σ} : SubsetEq (lty Σ) := λI φ1 φ2,
  ∀ v, □ φ1 v → φ2 v. *)
(*
Instance SubsetEq_type {Σ n} : SubsetEq (hoLtyO Σ n) := λI φ1 φ2,
  □ ∀ args v, φ1 args v → φ2 args v. *)

(* Definition subtype {Σ n} : sr_kind Σ n := λI ρ φ1 φ2,
  □ ∀ args v, φ1 args v → φ2 args v. *)


From D.Dot.lr Require Import dot_lty unary_lr lr_lemmasNoBinding.
Module HkDot2.
(* Include HoSemTypes2 VlSorts dlang_inst dot_lty. *)
Export HkDot.

Implicit Types (l : label) (p : path).

Inductive hty : nat → Type :=
  | hTTop : hty 0
  | hTBot : hty 0
  | hTAnd : hty 0 → hty 0 → hty 0
  | hTOr : hty 0 → hty 0 → hty 0
  | hTLater {n} : hty n → hty n
  | hTAll (S : hty 0) (T : hty 0) : hty 0
  | hTMu {n} (T : hty n) : hty n (* Changed *)
  | hTVMem l (T : hty 0) : hty 0
  | hTTMem {n} l (K : kind n) : hty n (* Changed *)
  | hTSel n p l : hty n (* Changed *)
  | hTPrim (B : base_ty): hty 0
  | hTSing p : hty 0
  (* New *)
  | hTLam {n} (T : hty n) : hty n.+1
  | hTApp {n} (T : hty n.+1) (p : path): hty n
with kind : nat → Type :=
  | kintv (L U : hty 0) : kind 0
  | kpi {n} (S : hty 0) (K : kind n) : kind n.+1.

Section semkinds.
  Context `{dlangG Σ}.

  (* Inductive kind {Σ} : nat → Type :=
    | kintv : olty Σ 0 → olty Σ 0 → kind 0
    | kpi n : olty Σ 0 → kind n → kind (S n).
  Global Arguments kind: clear implicits. *)

  (* Fixpoint sem {n} (k : kind Σ n) : sp_kind Σ n :=
    match k with
      | kintv φ1 φ2 => sp_s_kintv φ1 φ2
      | kpi n φ1 k' => spk_kpi φ1 (sem k')
    end. *)

  (* Notice the argument type is not used here. *)
  Inductive hoSTy {Σ} : nat → Type :=
    | TSWrap : olty Σ 0 → hoSTy 0
    | TSLam {n} : olty Σ 0 → hoSTy n → hoSTy (S n)
    | TSApp {n} : hoSTy (S n) → path → hoSTy n.

  (*
  Definition oLam {n} (τ : oltyO Σ n) : oltyO Σ (S n) :=
    (* vuncurry (λ v, τ.|[v/]). *)
    vuncurry (λ v, Olty (λ args ρ, τ args (v .: ρ))).
    (* Olty (λ args ρ, τ (vtail args) (vhead args .: ρ)). *)
  *)
  Lemma oLam_equiv1 {n τ} : oLam (Σ := Σ) (n := n) τ ≡
    Olty (λ args ρ, τ (vtail args) (vhead args .: ρ)).
  Proof. done. Qed.

  (* *not* equivalent! *)
  Lemma oLam_equiv2 {n τ} : oLam (Σ := Σ) (n := n) τ ≡
    vuncurry (λ v, τ.|[v/]).
  Proof.
    move=> args ρ v; rewrite /= /hsubst /hsubst_hoEnvD.
    asimpl.
    do 3 f_equiv.
  Abort.
  Fixpoint hoSTySem {n} (T : hoSTy n): olty Σ n :=
    match T with
    | TSWrap φ => φ
    | TSLam _ T => oLam (hoSTySem T)
    | TSApp T p => oTApp (hoSTySem T) p
    end.
End semkinds.
Arguments hoSTy: clear implicits.
End HkDot2.

(* These are abandoned experiments. *)
Module HoGenExperiments.
Import swap_later_impl HkDot2.

Section sec.
  Context `{dlangG Σ} `{HswapProp: SwapPropI Σ}.

  Lemma subtyping_spec i j Γ T1 T2 ρ :
    Γ s⊨ T1, i <: T2, j -∗
    s⟦ Γ ⟧* ρ -∗
    (∀ v, ▷^i oClose T1 ρ v → ▷^j oClose T2 ρ v).
  Proof.
    iIntros "#Hsub #Hg" (v).
    iApply ("Hsub" $! _ v with "Hg").
  Qed.

  Lemma subtyping_spec_swap i Γ T1 T2 ρ :
    Γ s⊨ T1, i <: T2, i -∗
    s⟦ Γ ⟧* ρ -∗
    ▷^i (∀ v, oClose T1 ρ v → oClose T2 ρ v).
  Proof using HswapProp.
    iIntros "#Hsub #Hg" (v).
    rewrite -mlaterN_impl.
    iApply (subtyping_spec with "Hsub Hg").
  Qed.

  Lemma sSkd_Intv' (L1 L2 U1 U2 : olty Σ 0) Γ i :
    Γ s⊨ L2, i <: L1, i -∗
    Γ s⊨ U1, i <: U2, i -∗
    Γ s⊨ sf_kintv L1 U1 <∷[ i ] sf_kintv L2 U2.
  Proof using HswapProp. by rewrite -!sstpkD_star_eq_sstp -sSkd_Intv. Qed.

  Lemma sK_Star' Γ (T : olty Σ 0) i :
    Γ s⊨ T ∷[ i ] sf_star.
  Proof using HswapProp.
    iApply sK_Sub. iApply sK_Sing.
    iApply sSkd_Intv'; [iApply sBot_Sub | iApply sSub_Top].
  Qed.

  Lemma sSkd_Pi' {n} (S1 S2 : olty Σ 0) (K1 K2 : sf_kind Σ n) Γ i :
    Γ s⊨ S2, i <: S1, i -∗
    oLaterN i (shift S2) :: Γ s⊨ K1 <∷[ i ] K2 -∗
    Γ s⊨ sf_kpi S1 K1 <∷[ i ] sf_kpi S2 K2.
  Proof using HswapProp. by rewrite -!sstpkD_star_eq_sstp -sSkd_Pi. Qed.

  Inductive htype : nat → Type :=
    | TWrap : ty → htype 0
    | TLam {n} : olty Σ 0 → htype n → htype (S n)
    | TApp {n} : htype (S n) → path → htype n.

  Fixpoint htype_to_hosty {n} (T : htype n) : hoSTy Σ n :=
    match T with
    | TWrap T => TSWrap V⟦T⟧
    | TLam φ T => TSLam φ (htype_to_hosty T)
    | TApp T v => TSApp (htype_to_hosty T) v
    end.
  Definition typeSem {n} (T : htype n) : hoEnvD Σ n := hoSTySem (htype_to_hosty T).

  Lemma sf_kpi_eq {n} (S : olty Σ 0) (φ1 φ2: hoLtyO Σ n.+1) (K : sf_kind Σ n) ρ :
    sf_kpi S K ρ φ1 φ2 ⊣⊢ □∀ v, oClose S ρ v → K (v .: ρ) (vcurry φ1 v) (vcurry φ2 v).
  Proof. done. Qed.

  Program Fixpoint sem_program {n} {struct n} : s_kind Σ n → sf_kind Σ n :=
    match n return _ with
    | 0 => λ k, match k with
      | s_kintv φ1 φ2 => sf_kintv φ1 φ2
      | s_kpi _ _ => _
      end
    | S n => λ k, match k with
      | s_kintv φ1 φ2 => _
      | s_kpi φ1 k' =>
        sf_kpi φ1 (sem_program (rew _ in k'))
      end
    end.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. intros. congruence. Defined.
  (* Derive Signature NoConfusion Subterm EqDec for kind. *)

  (* Derive Signature for kind.
  Equations sem_eq {n} : kind Σ n → sp_kind Σ n :=
    sem_eq (kintv φ1 φ2) := sp_s_kintv φ1 φ2;
    sem_eq (kpi n φ1 k') := spk_kpi φ1 (sem_eq k').

  Lemma unfold_sem_kintv φ1 φ2: sem_eq (kintv φ1 φ2) = sp_s_kintv φ1 φ2.
  Proof. by simp sem_eq. Qed. *)
End sec.
End HoGenExperiments.
