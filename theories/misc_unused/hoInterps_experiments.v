(* (* Must be loaded first, so that other modules can reset some flags. *)
Require Import Equations.Equations. *)
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
From D Require Import iris_prelude saved_interp_n.
From D Require Import saved_interp_dep asubst_intf dlang ty_interp_subst_lemmas.
From Coq Require FunctionalExtensionality.
Import EqNotations.

Set Suggest Proof Using.
Set Default Proof Using "Type".

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

Module Type HoSemTypes (Import VS : VlSortsFullSig) (Import LWP : LiftWp VS) (Import L : Lty VS LWP).
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

  Definition oCurry {n} {A : ofeT} (Φ : vec vl (S n) -> A) :
    vl -d> vec vl n -d> A := vcurry Φ.

  Definition oUncurry {n} {A : ofeT} (Φ : vl → vec vl n → A) :
    vec vl (S n) -d> A := vuncurry Φ.
  Definition oLaterN {n} i (τ : olty Σ n) := Olty (eLater i τ).
End saved_ho_sem_type_extra.

Definition hoLty Σ n := vec vl n -> lty Σ.
Definition hoLtyO Σ n := vec vl n -d> ltyO Σ.

Definition envApply {Σ n} : oltyO Σ n → env → hoLtyO Σ n :=
  λ T, flip T.

(** The semantics of a kind includes a predicate on types, and a subtype predicate.
  *)
(* XXX make these non-expansive? *)
Notation skind Σ n := (∀ (i : nat), env → hoLty Σ n → iProp Σ).
Notation srelkind Σ n := (env → hoLtyO Σ n → hoLtyO Σ n → iProp Σ).

(* Semantic Full Kind. *)
Record sfkind Σ n := Sfkind {
  sfkind_car :> skind Σ n;
  sfkind_sub : srelkind Σ n;
}.
Global Arguments Sfkind {_ _} _ _.
Global Arguments sfkind_car {_ _} _ _ _ : simpl never.
Global Arguments sfkind_sub {_ _} _ _ _ _ : simpl never.

(** Kinded, indexed subtyping *)
Program Definition sstpk `{dlangG Σ} {n} i j Γ T1 T2 (K : sfkind Σ n) : iProp Σ :=
  □∀ ρ, s⟦Γ⟧*ρ → sfkind_sub K ρ (envApply (oLaterN i T1) ρ) (envApply (oLaterN j T2) ρ).
(* :: is at level 60. *)
(* Notation "Γ s⊨k T1 , i <: T2 , j ∷ K" := (sstpk i j Γ T1 T2 K)
  (at level 74, i, j at level 59, T1, T2, i at next level). *)
Notation "Γ s⊨ T1 , i <: T2 , j ∷ K" := (sstpk i j Γ T1 T2 K)
  (at level 74, i, j, T1, T2 at next level).

(* XXX Should we delay [T] as well? Yes, based on [iSel_Sub]/[iSub_Sel].
Should we delay K?*)
(* V1: delay K and rely on swaps to make that affect all types. *)
(* Definition sktp `{dlangG Σ} {n} i Γ T (K : sfkind Σ n) : iProp Σ :=
  □∀ ρ, s⟦Γ⟧*ρ → ▷^i K ρ T. *)
(* V2: push the delay down. *)
Definition sktp `{dlangG Σ} {n} i Γ T (K : sfkind Σ n) : iProp Σ :=
  □∀ ρ, s⟦Γ⟧*ρ → K i ρ (envApply (oLaterN i T) ρ).
(* XXX What delays are wanted here? *)
(* Definition ssktp `{dlangG Σ} {n} i Γ (K1 K2 : sfkind Σ n) : iProp Σ :=
  □∀ ρ T, s⟦Γ⟧*ρ → ▷^i K1 ρ (envApply T ρ) → ▷^i K2 ρ (envApply T ρ). *)
Definition ssktp `{dlangG Σ} {n} i Γ (K1 K2 : sfkind Σ n) : iProp Σ :=
  □∀ ρ (T : olty Σ n), s⟦Γ⟧*ρ → K1 i ρ (envApply T ρ) → K2 i ρ (envApply T ρ).

End HoSemTypes.

From D.Dot Require Import dot_lty unary_lr.
Module HkDot.
Include HoSemTypes VlSorts dlang_inst dot_lty.

Section semkinds.
  Context `{dlangG Σ}.

  Definition subtype {n} : srelkind Σ n := λI ρ φ1 φ2,
    □ ∀ args v, φ1 args v → φ2 args v.

  Definition skstar : skind Σ 0 := λI i ρ φ, True.
  Definition srstar : srelkind Σ 0 := λ ρ φ1 φ2,
    (□ ∀ v, oClose φ1 v → oClose φ2 v)%I.
  Definition sstar : sfkind Σ 0 := Sfkind skstar srstar.

  (* Show that kinded subtyping correctly generalizes the existing kind-*
  subtyping. *)
  Lemma sstpk_star_eq_sstp Γ i j T1 T2 :
    Γ s⊨ T1 , i <: T2 , j ∷ sstar ⊣⊢ Γ s⊨ T1 , i <: T2 , j.
  Proof.
    rewrite /sstpk /sfkind_sub/= /srstar; iSplit; iIntros "/= #Hsub !>" (ρ).
    by iIntros (v) "#Hg"; iApply ("Hsub" $! ρ with "Hg").
    by iIntros "#Hg" (v) "!>"; iApply ("Hsub" $! ρ v with "Hg").
  Qed.

  Definition skpi {n} (φArg : olty Σ 0) (K : skind Σ n) : skind Σ (S n) :=
    λI i ρ φ, □∀ arg, oClose φArg ρ arg → K i (arg .: ρ) (vcurry φ arg).
  Definition srpi {n} (φArg : olty Σ 0) (Kr : srelkind Σ n) : srelkind Σ (S n) :=
    λI ρ φ1 φ2, □∀ arg, oClose φArg ρ arg → Kr (arg .: ρ) (vcurry φ1 arg) (vcurry φ2 arg).
  Definition spi {n} (φArg : olty Σ 0) (K : sfkind Σ n) : sfkind Σ (S n) :=
    Sfkind (skpi φArg (sfkind_car K)) (srpi φArg (sfkind_sub K)).

  Definition fold_srelkind (base : srelkind Σ 0) : ∀ n, vec (olty Σ 0) n → srelkind Σ n :=
    vec_fold base (@srpi).
  Definition subtype_w_expKind : ∀ n, vec (olty Σ 0) n → srelkind Σ n :=
    fold_srelkind srstar.
  (* Definition eqtype_w_expKind : ∀ n, vec (olty Σ 0) n → srelkind Σ n :=
    fold_srelkind kind_star_eqtype. *)

  (* The point of Sandro's kind syntax is to use this only at kind 0. *)
  Program Definition skintv (φ1 φ2 : olty Σ 0) : skind Σ 0 := λI i ρ φ,
    subtype ρ (envApply (oLaterN i φ1) ρ) φ
    (* subtype ρ (envApply (oLaterN (S i) φ1) ρ) (oLater i φ). *)
    ∧
    (* subtype ρ (oLaterN i φ) (envApply (oLaterN (S i) φ2) ρ). *)
    subtype ρ φ (envApply (oLaterN i φ2) ρ).
  Definition sintv (φ1 φ2 : olty Σ 0) : sfkind Σ 0 :=
    Sfkind (skintv φ1 φ2) srstar.

  Inductive kind {Σ} : nat → Type :=
    | kintv : olty Σ 0 → olty Σ 0 → kind 0
    | kpi n : olty Σ 0 → kind n → kind (S n).
  Global Arguments kind: clear implicits.

  Fixpoint sem {n} (k : kind Σ n) : skind Σ n :=
    match k with
      | kintv φ1 φ2 => skintv φ1 φ2
      | kpi n φ1 k' => skpi φ1 (sem k')
    end.

  (* Notice the argument type is not used here. *)
  Inductive hoSTy {Σ} : nat → Type :=
    | TSWrap : olty Σ 0 → hoSTy 0
    | TSLam {n} : olty Σ 0 → hoSTy n → hoSTy (S n)
    | TSApp {n} : hoSTy (S n) → path → hoSTy n.

  Definition oLam {n} (τ : oltyO Σ n) : oltyO Σ (S n) :=
    (* vuncurry (λ v, τ.|[v/]). *)
    vuncurry (λ v, Olty (λ args ρ, τ args (v .: ρ))).
    (* Olty (λ args ρ, τ (vtail args) (vhead args .: ρ)). *)
  Lemma oLam_equiv1 {n τ} : oLam (n := n) τ ≡
    Olty (λ args ρ, τ (vtail args) (vhead args .: ρ)).
  Proof. done. Qed.

  (* *not* equivalent! *)
  Lemma oLam_equiv2 {n τ} : oLam (n := n) τ ≡
    vuncurry (λ v, τ.|[v/]).
  Proof.
    move=> args ρ v; rewrite /= /hsubst /hsubst_hoEnvD.
    asimpl.
    do 3 f_equiv.
  Abort.

  Definition oTApp {n} (τ : oltyO Σ (S n)) v : olty Σ n := vcurry τ v.
  Definition oTAppP {n} (τ : oltyO Σ (S n)) (p : path) : olty Σ n :=
    Olty (λ args ρ v, path_wp p.|[ρ] (λ w, vcurry τ w args ρ v)).

  Lemma swap_oLam_oLater {n} (τ : olty Σ n) :
    oLater (oLam τ) ≡ oLam (oLater τ).
  Proof. done. Qed.

  Lemma swap_oTApp_oLater {n} (τ : olty Σ (S n)) v:
    oLater (oTApp τ v) ≡ oTApp (oLater τ) v.
  Proof. done. Qed.

  Fixpoint hoSTySem {n} (T : hoSTy n): olty Σ n :=
    match T with
    | TSWrap φ => φ
    | TSLam _ T => oLam (hoSTySem T)
    | TSApp T p => oTAppP (hoSTySem T) p
    end.
End semkinds.
Arguments hoSTy: clear implicits.
End HkDot.

From D Require swap_later_impl.
(* These are "bad" experiments. *)
Module HoGenExperimnents.
Import swap_later_impl HkDot.
Section sec.
  Context `{!CTyInterp Σ}.
  Context `{dlangG Σ} `{HswapProp: SwapPropI Σ}.

  Definition srstar1 : srelkind Σ 0 := subtype.
  Lemma srstar_eq ρ φ1 φ2 :
    srstar1 ρ φ1 φ2 ≡ srstar ρ φ1 φ2.
  Proof.
    rewrite /srstar1 /srstar /subtype /vclose.
    apply intuitionistically_proper, equiv_spec; split. by iIntros "H".
    iIntros "H" (args). by rewrite (vec_vnil args).
  Qed.

  (* Definition skLaterN {Σ n} i (K : skind Σ n) : skind Σ n :=
    λ ρ φ, K ρ (oLaterN i φ). *)
  (* Definition srLaterN {Σ n} i j (K : srelkind Σ n) : srelkind Σ n :=
    λ ρ T1 T2, K ρ (oLaterN i T1) (oLaterN j T2). *)
  (* Definition sfLaterN {n} i (K : sfkind Σ n) : sfkind Σ n :=
    Sfkind (skLaterN i K) K. *)

  (* Definition sstpk `{dlangG Σ} {n} i j Γ τ₁ τ₂ (K : sfkind Σ n) : iProp Σ :=
    □∀ ρ, s⟦Γ⟧*ρ → srLaterN i j (sfkind_sub K) ρ τ₁ τ₂. *)
  (* Definition semEquiv {n} : srelkind Σ n := λI ρ (φ1 φ2 : olty Σ n),
    □ ∀ args v, φ1 args ρ v ↔ φ2 args ρ v. *)
  (* Definition kind_star_eqtype : srelkind Σ 0 := λ ρ φ1 φ2,
    (□ ∀ v, oClose φ1 ρ v ↔ oClose φ2 ρ v)%I. *)


  Definition sstpk1 {n} i Γ (T1 T2 : oltyO Σ n) (K : sfkind Σ n) : iProp Σ :=
    □∀ ρ, s⟦Γ⟧*ρ → ▷^i sfkind_sub K ρ (envApply T1 ρ) (envApply T2 ρ).
  Lemma sstpk1_star_eq_sstp Γ i T1 T2 :
    sstpk1 i Γ T1 T2 sstar ⊣⊢ Γ s⊨ T1 , i <: T2 , i.
  Proof using HswapProp.
    rewrite /sstpk1 /sfkind_sub/= /srstar.
    iSplit; iIntros "/= #Hsub !>" (ρ); [iIntros (v)|]; iIntros "#Hg".
    iSpecialize ("Hsub" $! ρ with "Hg"); iSpecialize ("Hsub" $! v).
    rewrite -mlaterN_pers laterN_impl.
    by iApply "Hsub".
    rewrite -mlaterN_pers; iIntros (v) "!>"; rewrite -mlaterN_impl.
    iDestruct "Hsub" as "#Hsub".
    iApply ("Hsub" $! ρ v with "Hg").
  Qed.

  (* Inductive kind : nat → Type :=
    | kintv : ty → ty → kind 0
    | kpi n : ty → kind n → kind (S n). *)


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

  Lemma K_App_Lam {n} (argT : olty Σ 0) (φ1 φ2: hoLtyO Σ (S n)) (K : srelkind Σ n) ρ :
    srpi argT K ρ φ1 φ2 ⊣⊢ (□∀ v, oClose argT ρ v → K (v .: ρ) (vcurry φ1 v) (vcurry φ2 v))%I.
  Proof. done. Qed.
  (** XXX Need a subtyping judgment to throw in environments... *)

  (* Here, we inherit eta from the metalanguage, in both directions. *)
  (* Er, let's please carry it closer to the syntax? *)
  Lemma eta1 {n} argT (φ : hoLtyO Σ (S n)) ρ : srpi argT subtype ρ φ (vuncurry (vcurry φ)).
  Proof.
    rewrite /srpi /subtype.
    iIntros "!> * #Harg !>" (args v) "$".
  Qed.

  Lemma eta2 {n} argT (φ : hoLtyO Σ (S n)) ρ : srpi argT subtype ρ (vuncurry (vcurry φ)) φ.
  Proof.
    rewrite /srpi /subtype.
    iIntros "!> * #Harg !>" (args v) "$".
  Qed.

  (* Lemma eta {n} argT (φ : olty Σ (S n)) ρ : srpi argT semEquiv ρ φ (vuncurry (vcurry φ)).
  Proof.
    rewrite /srpi /semEquiv.
    iIntros "!> * #Harg !> **". rewrite -(iff_refl emp%I). done.
  Qed. *)

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

Module dot_experiments.
Import HkDot.
(* Include TyInterpLemmas VlSorts dlang_inst.
Export ty_interp_lemmas. *)

Section sec.
  Context `{!savedHoSemTypeG Σ} `{!dlangG Σ} `{CTyInterp Σ}.

  Definition dm_to_type (d : dm) n (ψ : hoD Σ n) : iProp Σ :=
    (∃ s σ, ⌜ d = dtysem σ s ⌝ ∧ s ↗n[ σ, n ] ψ)%I.
  Notation "d ↗n[ n ] φ" := (dm_to_type d n φ) (at level 20).
  Global Arguments dm_to_type: simpl never.

  (* [K]'s argument must ignore [ρ]. Patch the definition of skind instead. *)
  Notation HoLty φ := (λ args, Lty (λI v, φ args v)).
  Definition packHoLtyO {Σ n} φ : hoLtyO Σ n := HoLty (λI args v, □ φ args v).

  Definition def_interp_tmem {n} (K : skind Σ n): envPred dm Σ :=
    (* λI ρ d, ∃ (φ : hoLtyO Σ n), d.|[ρ] ↗n[ n ] φ ∧ K 0 ρ φ. *)
    λI ρ d, ∃ (φ : hoD Σ n), d.|[ρ] ↗n[ n ] φ ∧ K 0 ρ (packHoLtyO φ).
  Definition def_interp_tmem_spec (φ1 φ2 : olty Σ 0) : envPred dm Σ :=
    def_interp_tmem (skintv (oLater φ1) (oLater φ2)).
End sec.

Notation "d ↗n[ n ] φ" := (dm_to_type d n φ) (at level 20).
End dot_experiments.
