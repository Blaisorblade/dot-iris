(* (* Must be loaded first, so that other modules can reset some flags. *)
Require Import Equations.Equations. *)
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
From D Require Import iris_prelude saved_interp_n.
From D Require Import saved_interp_dep asubst_intf dlang ty_interp_subst_lemmas.
From Coq Require FunctionalExtensionality.
Import EqNotations.

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

(* *)
Module simple.
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
End simple.

Module Type HoSemTypes (Import VS : VlSortsFullSig) (Import LWP : LiftWp VS).
Include Lty VS LWP.

(* XXX Good names? *)
Notation iPred T Σ := (T → iProp Σ).
Notation iPredO T Σ := (T -d> iPropO Σ).

Section saved_ho_sem_type_extra.
  (* Context `{!savedHoSemTypeG Σ}. *)
  Context {Σ : gFunctors}.

  Implicit Types (Ψ : packedHoEnvD Σ).

  (** ** Accessing saved HO predicates. *)
  Definition packedHoEnvD_arity : packedHoEnvD Σ -n> natO := packedHoEnvPred_arity.

  Program Definition unNext: laterO (iPropO Σ) -n> iPropO Σ :=
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

  (** The semantics of a kind includes a predicate on types, and a subtype predicate.
   *)
  (* XXX make these non-expansive. *)
  Definition skind Σ n := env → olty Σ n →  iProp Σ.
  Definition srelkind Σ n := env → olty Σ n → olty Σ n → iProp Σ.

  (* Semantic Full Kind. *)
  Record sfkind Σ n := Sfkind {
    sfkind_car :> skind Σ n;
    sfkind_sub :> srelkind Σ n;
  }.
  Global Arguments Sfkind {_ _} _ _.
  Global Arguments sfkind_car {_ _} _ _ _ : simpl never.
  Global Arguments sfkind_sub {_ _} _ _ _ _ : simpl never.

  (* Definition app {n} (F : sfkind Σ n) (A : hoD Σ n) := F A. *)
  Definition app1 {n} (F : sfkind Σ n) : skind Σ n := F.
  Definition app2 {n} (F : sfkind Σ n) : srelkind Σ n := F.

  Definition subtype {n} : srelkind Σ n := λ ρ (φ1 φ2 : olty Σ n),
    (□ ∀ (args : vec vl n) v, ⌜ nclosed_vl v 0 ⌝ -∗
      φ1 args ρ v -∗ φ2 args ρ v)%I.
  Definition semEquiv {n} : srelkind Σ n := λ ρ (φ1 φ2 : olty Σ n),
    (□ ∀ (args : vec vl n) v, ⌜ nclosed_vl v 0 ⌝ -∗
      φ1 args ρ v ∗-∗ φ2 args ρ v)%I.

  Notation D := (iPred vl Σ).

  Definition kind_star_subtype1 : srelkind Σ 0 := subtype.
  Definition kind_star_subtype : srelkind Σ 0 := λ ρ φ1 φ2,
    (□ ∀ v, ⌜ nclosed_vl v 0 ⌝ -∗ vclose (oApp φ1) ρ v -∗ vclose (oApp φ2) ρ v)%I.
  Definition kind_star_eqtype : srelkind Σ 0 := λ ρ φ1 φ2,
    (□ ∀ v, ⌜ nclosed_vl v 0 ⌝ -∗ vclose (oApp φ1) ρ v ∗-∗ vclose (oApp φ2) ρ v)%I.

  Lemma kind_star_subtype_eq ρ φ1 φ2 :
    kind_star_subtype1 ρ φ1 φ2 ≡ kind_star_subtype ρ φ1 φ2.
  Proof.
    rewrite /kind_star_subtype1 /kind_star_subtype /subtype /vclose.
    apply intuitionistically_proper, equiv_spec; split. by iIntros "H".
    iIntros "H" (args). by rewrite (vec_vnil args).
  Qed.

  Program Definition ocurry {n} (Φ : olty Σ (S n)) : vl -d> oltyO Σ n :=
    λ v, Olty (λ args, vcurry (oApp Φ) v args).

  Program Definition ouncurry {n} (Φ : vl -d> oltyO Σ n) : olty Σ (S n) :=
    Olty (λ args, vuncurry (λ v, oApp (Φ v)) args).

  Definition oclose (φ : olty Σ 0) : env → iPred vl Σ := φ vnil.

  Definition skpi {n} (φArg : olty Σ 0) (K : skind Σ n) : skind Σ (S n) :=
    λ ρ φ, (□∀ arg, vclose (oApp φArg) ρ arg → K ρ (ocurry φ arg))%I.

  (* A possible sketch of kinded subtyping for lambdas? *)
  Definition srpi {n} (φArg : olty Σ 0) (Kr : srelkind Σ n) : srelkind Σ (S n) :=
    λ ρ φ1 φ2, (□∀ arg, vclose (oApp φArg) ρ arg -∗ Kr ρ (ocurry φ1 arg) (ocurry φ2 arg))%I.

  Definition spi {n} (φArg : olty Σ 0) (K : sfkind Σ n) : sfkind Σ (S n) :=
    Sfkind (skpi φArg (sfkind_car K)) (srpi φArg (sfkind_sub K)).

  Definition fold_srelkind (base : srelkind Σ 0) : ∀ n, vec (olty Σ 0) n → srelkind Σ n :=
    vec_fold base (@srpi).
  Definition subtype_w_expKind : ∀ n, vec (olty Σ 0) n → srelkind Σ n :=
    fold_srelkind kind_star_subtype.
  Definition eqtype_w_expKind : ∀ n, vec (olty Σ 0) n → srelkind Σ n :=
    fold_srelkind kind_star_eqtype.

  (* The point of Sandro's kind syntax is to use this only at kind 0. *)
  (* Definition sktmem {n} (φ1 φ2 : hoD Σ n) φ :=
    (subtype n 1 1 φ1 φ ∧ subtype n 1 1 φ φ)%I. *)
  Definition skintv (φ1 φ2 : olty Σ 0) : skind Σ 0 := λ ρ φ,
    (subtype ρ φ1 φ ∧ subtype ρ φ φ2)%I.
  Definition sintv (φ1 φ2 : olty Σ 0) : sfkind Σ 0 :=
    Sfkind (skintv φ1 φ2) kind_star_subtype.
  (* Next Obligation.  move=>????? Heq. f_equiv. exact: Heq. solve_proper_ho. *)

  Definition oLaterN {n} i (τ : olty Σ n) := Olty (eLater i τ).
  Definition skLaterN {n} i (K : skind Σ n) : skind Σ n :=
    λ ρ φ, K ρ (oLaterN i φ).
  Definition sfLaterN {n} i (K : sfkind Σ n) : sfkind Σ n :=
    Sfkind (skLaterN i K) K.

  Definition sktmem (φ1 φ2 : olty Σ 0) : skind Σ 0 :=
    skLaterN 1 (skintv (oLaterN 1 φ1) (oLaterN 1 φ2)).

  (* Inductive kind : nat → Type :=
    | kintv : ty → ty → kind 0
    | kpi n : ty → kind n → kind (S n). *)

  Inductive kind {Σ} : nat → Type :=
    | kintv : olty Σ 0 → olty Σ 0 → kind 0
    | kpi n : olty Σ 0 → kind n → kind (S n).
  Global Arguments kind: clear implicits.

  Fixpoint sem {n} (k : kind Σ n) : skind Σ n :=
    match k with
      | kintv φ1 φ2 => skintv φ1 φ2
      | kpi n φ1 k' => skpi φ1 (sem k')
    end.

  Inductive hoSTy {Σ} : nat → Type :=
    | TSWrap : hoEnvD Σ 0 → hoSTy 0
    | TSLam n : hoEnvD Σ 0 → hoSTy n → hoSTy (S n)
    | TSApp n : hoSTy (S n) → vl → hoSTy n.

  (* Olty needed, to give both semantic substitution and extra attributes. *)

  Fixpoint hoSTySem {n} (T : hoSTy n): hoEnvD Σ n :=
    match T with
    | TSWrap φ => φ
    | TSLam n' φ T' =>
      (* vuncurry (λ v, hoSTySem T') *)
      (* XXX Now I need semantic substitution. *)
      (* vuncurry (A := envD Σ) (λ v, (hoSTySem T').|[v/]) *)
      (* Alternatives: *)
      vuncurry (A := envD Σ) (λ v args ρ, hoSTySem T' args (v .: ρ))
      (* λ args ρ, hoSTySem T' (vtail args) (vhead args .: ρ) *)
    | TSApp n' T' v =>
      vcurry (hoSTySem T') v
    end.
End saved_ho_sem_type_extra.
Arguments hoSTy: clear implicits.
End HoSemTypes.

Module Type HoGenExperimnents (Import VS : VlSortsFullSig) (Import LWP : LiftWp VS).
Include HoSemTypes VS LWP.
Include TyInterpLemmas VS LWP.
Section sec.
  Context `{TyInterp ty Σ}.

  Inductive htype : nat → Type :=
    | TWrap : ty → htype 0
    | TLam n : hoEnvD Σ 0 → htype n → htype (S n)
    | TApp n : htype (S n) → vl → htype n.

  Fixpoint htype_to_hosty {n} (T : htype n) : hoSTy Σ n :=
    match T with
    | TWrap T' => TSWrap (vopen (ty_interp T'))
    | TLam n' φ T' => TSLam n' φ (htype_to_hosty T')
    | TApp n' T' v => TSApp n' (htype_to_hosty T') v
    end.
  Definition typeSem {n} (T : htype n) : hoEnvD Σ n := hoSTySem (htype_to_hosty T).

  Lemma K_App_Lam {n} (argT : olty Σ 0) (φ1 φ2: olty Σ (S n)) (K : srelkind Σ n) ρ :
    srpi argT K ρ φ1 φ2 ⊣⊢ (□∀ v, oclose argT ρ v -∗ K ρ (ocurry φ1 v) (ocurry φ2 v))%I.
  Proof. done. Qed.
  (** XXX Need a subtyping judgment to throw in environments... *)

  (* Here, we inherit eta from the metalanguage, in both directions. *)
  (* Er, let's please carry it closer to the syntax? *)
  Lemma eta1 {n} argT (φ : olty Σ (S n)) ρ : srpi argT subtype ρ φ (ouncurry (ocurry φ)).
  Proof.
    rewrite /srpi /subtype.
    iIntros "!> * #Harg !>" (args v Hcl) "$".
  Qed.

  Lemma eta {n} argT (φ : olty Σ (S n)) ρ : srpi argT semEquiv ρ φ (ouncurry (ocurry φ)).
  Proof.
    rewrite /srpi /semEquiv.
    iIntros "!> * #Harg !> **"; rewrite -wand_iff_refl. done.
  Qed.

  Program Fixpoint sem_program {n} {struct n} : kind Σ n → skind Σ n :=
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
  Next Obligation. intros. congruence. Defined.
  (* Derive Signature NoConfusion Subterm EqDec for kind. *)

  (* Derive Signature for kind.
  Equations sem_eq {n} : kind Σ n → skind Σ n :=
    sem_eq (kintv φ1 φ2) := skintv φ1 φ2;
    sem_eq (kpi n φ1 k') := skpi φ1 (sem_eq k').

  Lemma unfold_sem_kintv φ1 φ2: sem_eq (kintv φ1 φ2) = skintv φ1 φ2.
  Proof. by simp sem_eq. Qed. *)
End sec.
End HoGenExperimnents.

From D.Dot Require syn dlang_inst.

Module dot_experiments.
Import syn dlang_inst.
Include HoSemTypes VlSorts dlang_inst.
Include TyInterpLemmas VlSorts dlang_inst.

Section sec.
  Context `{!savedHoSemTypeG Σ} `{!dlangG Σ} `{TyInterp ty Σ}.
  (* Implicit Types (interp : envD Σ) (φ : D). *)

  Definition dm_to_type (d : dm) n (ψ : hoD Σ n) : iProp Σ :=
    (∃ s σ, ⌜ d = dtysem σ s ⌝ ∧ s ↗n[ σ, n ] ψ)%I.
  Notation "d ↗n[ n ] φ" := (dm_to_type d n φ) (at level 20).
  Global Arguments dm_to_type: simpl never.

  (* Definition def_interp_tmem {n} : skind Σ n → envPred dm Σ :=
    λ K ρ d, (∃ φ, d.|[ρ] ↗n[ n ] φ ∧ K ρ (Olty φ))%I.
  Definition def_interp_tmem_spec (φ1 φ2 : hoD Σ 0) : envPred dm Σ :=
    def_interp_tmem (sktmem φ1 φ2). *)
End sec.

Notation "d ↗n[ n ] φ" := (dm_to_type d n φ) (at level 20).
End dot_experiments.
