(* (* Must be loaded first, so that other modules can reset some flags. *)
Require Import Equations.Equations. *)
From Coq Require FunctionalExtensionality.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
From D Require Import iris_prelude.
From D Require Import saved_interp_dep asubst_intf asubst_base dlang lty.
From D Require Import swap_later_impl.
From D.Dot.lr Require dot_lty unary_lr lr_lemmasNoBinding typeExtractionSem.

Import EqNotations.

Set Suggest Proof Using.
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (Σ : gFunctors) .
(** ssreflect postfix notation for the successor and predecessor functions.
SSreflect uses "pred" for the generic predicate type, and S as a local bound
variable.*)
Notation succn := Datatypes.S.
Notation predn := Peano.pred.

Notation "n .+1" := (succn n) (at level 2, left associativity,
  format "n .+1") : nat_scope.
Notation "n .+2" := n.+1.+1 (at level 2, left associativity,
  format "n .+2") : nat_scope.
Notation "n .+3" := n.+2.+1 (at level 2, left associativity,
  format "n .+3") : nat_scope.
Notation "n .+4" := n.+2.+2 (at level 2, left associativity,
  format "n .+4") : nat_scope.

Notation "n .-1" := (predn n) (at level 2, left associativity,
  format "n .-1") : nat_scope.
Notation "n .-2" := n.-1.-1 (at level 2, left associativity,
  format "n .-2") : nat_scope.


Module Type HoSemTypes (Import VS : VlSortsFullSig) (Import LWP : LiftWp VS) (Import L : Lty VS LWP).

Definition hoLty Σ n := vec vl n → lty Σ.
Definition hoLtyO Σ n := vec vl n -d> ltyO Σ.

Definition envApply {Σ n} : oltyO Σ n → env → hoLtyO Σ n :=
  λ T, flip T.
Global Instance Proper_envApply n: Proper ((≡) ==> (=) ==> (≡)) (envApply (Σ := Σ) (n := n)).
Proof. solve_proper_ho. Qed.

Definition oCurry {n} {A : ofeT} (Φ : vec vl n.+1 → A) :
  vl -d> vec vl n -d> A := vcurry Φ.

Definition oUncurry {n} {A : ofeT} (Φ : vl → vec vl n → A) :
  vec vl n.+1 -d> A := vuncurry Φ.
Definition oLaterN {Σ n} i (τ : olty Σ n) := Olty (eLater i τ).

(** An inductive representation of gHkDOT semantic kinds. *)
Inductive s_kind {Σ} : nat → Type :=
  | s_kintv : olty Σ 0 → olty Σ 0 → s_kind 0
  | s_kpi n : olty Σ 0 → s_kind n → s_kind n.+1.
Global Arguments s_kind: clear implicits.

(** Alternative inductive representation of gHkDOT semantic kinds. *)
Record spine_s_kind {Σ} {n : nat} : Type := SpineSK {
  spine_kargs : vec (olty Σ 0) n;
  spine_L : olty Σ 0;
  spine_U : olty Σ 0;
}.
Arguments spine_s_kind : clear implicits.

(** Semantic kinds can be interpreted into predicates. *)
(** Semantic Kinds as unary Predicates. *)
Notation sp_kind Σ n := (env → iPPred (hoLtyO Σ n) Σ).
Notation SpKind K := (λ ρ, IPPred (λI T, K ρ T)).

(** Semantic Kinds as relations. *)
Notation sr_kind Σ n := (env → hoLtyO Σ n → iPPred (hoLtyO Σ n) Σ).
Notation SrKind K := (λ ρ T1, IPPred (λI T2, K ρ T1 T2)).

Notation iRel P Σ := (P Σ → P Σ → iProp Σ).
Definition subtype_lty {Σ} : iRel ltyO Σ := λI φ1 φ2,
  □ ∀ v, φ1 v → φ2 v.
Global Instance: NonExpansive2 (subtype_lty (Σ := Σ)).
Proof. solve_proper_ho. Qed.

Infix "⊆" := subtype_lty : bi_scope.
Notation "X ⊆@{ Σ } Y" := (subtype_lty (Σ := Σ) X Y) (at level 70, only parsing) : bi_scope.
Notation "X ⊆ Y ⊆ Z" := (X ⊆ Y ∧ Y ⊆ Z)%I : bi_scope.
Notation "X ⊆ Y ⊆ Z ⊆ W" := (X ⊆ Y ∧ Y ⊆ Z ∧ Z ⊆ W)%I (at level 70, Y, Z at next level) : bi_scope.

(** Semantic Full Kind. *)
Record sf_kind {Σ n} := SfKind {
  sf_kind_sub :> sr_kind Σ n;
  sf_kind_sub_ne ρ :> NonExpansive2 (sf_kind_sub ρ);
  sf_kind_sub_trans ρ T1 T2 T3 :
    sf_kind_sub ρ T1 T2 -∗
    sf_kind_sub ρ T2 T3 -∗
    sf_kind_sub ρ T1 T3;
  sf_kind_sub_quasi_refl_1 ρ T1 T2 :
    sf_kind_sub ρ T1 T2 -∗
    sf_kind_sub ρ T1 T1;
  sf_kind_sub_quasi_refl_2 ρ T1 T2 :
    sf_kind_sub ρ T1 T2 -∗
    sf_kind_sub ρ T2 T2;
}.
Global Arguments sf_kind : clear implicits.
Global Arguments sf_kind_sub {_ _} !_ /.
Add Printing Constructor sf_kind.
Global Arguments SfKind {_ _} _.

(* This is really properness of sf_kind_sub; but it's also proper over the
first argument K. Maybe that's worth a wrapper with swapped arguments. *)
Global Instance Proper_sfkind {Σ n} (K : sf_kind Σ n) ρ :
  Proper ((≡) ==> (≡) ==> (≡)) (K ρ).
Proof.
  move=> T1 T2 /equiv_dist HT U1 U2 /equiv_dist HU.
  apply /equiv_dist => m. exact: sf_kind_sub_ne.
Qed.
Global Lemma Proper_sfkind' {Σ n} (K : sf_kind Σ n) ρ T1 T2 :
  T1 ≡ T2 → K ρ T1 T1 ≡ K ρ T2 T2.
Proof. intros Heq. by apply Proper_sfkind. Qed.

Global Instance Proper_sfkind_A {Σ n} (K : sf_kind Σ n) ρ :
  Proper (pointwise_relation _ (≡) ==> pointwise_relation _ (≡) ==> (≡)) (K ρ).
Proof. apply Proper_sfkind. Qed.

Global Instance vcurry_ne vl n A m : Proper (dist m ==> (=) ==> dist m) (@vcurry vl n A).
Proof. solve_proper_ho. Qed.

Section kinds_types.
  Context {Σ}.

  Lemma subtype_refl {T}: (T ⊆@{Σ} T)%I.
  Proof. iIntros "!> * $". Qed.

  Lemma subtype_trans {T1} T2 {T3} :
    T1 ⊆ T2 -∗ T2 ⊆ T3 -∗ T1 ⊆@{Σ} T3.
  Proof.
    iIntros "#Hs1 #Hs2 !>" (v) "#HT1".
    iApply ("Hs2" with "(Hs1 HT1)").
  Qed.

  Definition sp_s_kintv (L U : olty Σ 0) : spine_s_kind Σ 0 := SpineSK vnil L U.
  Definition sp_s_kpi {n} (S : olty Σ 0) (K : spine_s_kind Σ n) : spine_s_kind Σ n.+1 :=
    SpineSK (vcons S (spine_kargs K)) (spine_L K) (spine_U K).

  Definition sp_kintv (L U : olty Σ 0) : sp_kind Σ 0 := SpKind (λI ρ φ,
    oClose L ρ ⊆ oClose φ ⊆ oClose U ρ).

  Definition sr_kintv (L U : olty Σ 0) : sr_kind Σ 0 := SrKind (λI ρ φ1 φ2,
    oClose L ρ ⊆ oClose φ1 ⊆ oClose φ2 ⊆ oClose U ρ).

  Lemma sr_kintv_refl L U ρ φ : sp_kintv L U ρ φ -∗ sr_kintv L U ρ φ φ.
  Proof. iIntros "($ & $)". by rewrite -subtype_refl. Qed.

  Program Definition sf_kintv (L U : olty Σ 0) : sf_kind Σ 0 :=
    SfKind (sr_kintv L U) ltac:(solve_proper_ho) _ _ _.
  Next Obligation.
    iIntros "* ($&HLT1&_) (_ & HT2T3 & $)".
    iApply (subtype_trans (oClose T2) with "HLT1 HT2T3").
  Qed.
  Next Obligation.
    intros; rewrite -sr_kintv_refl; iIntros "* /= ($ & B & C)".
    iApply (subtype_trans with "B C").
  Qed.
  Next Obligation.
    intros; rewrite -sr_kintv_refl; iIntros "* /= #(A & B & $)".
    iApply (subtype_trans with "A B").
  Qed.

  Program Definition sf_kpi {n} (S : olty Σ 0) (K : sf_kind Σ n) : sf_kind Σ n.+1 :=
    SfKind
      (* (SpKind (λI ρ φ,
        □∀ arg, S vnil ρ arg →
        sf_kind_car K (arg .: ρ) (vcurry φ arg))) *)
      (SrKind (λI ρ φ1 φ2,
        □∀ arg, S vnil ρ arg →
        K (arg .: ρ) (vcurry φ1 arg) (vcurry φ2 arg))) _ _ _ _.
  (* Next Obligation.
    move=> n S K ρ m T1 T2 HT /=.
    have ?: ∀ ρ, NonExpansive (sf_kind_car K ρ) by apply sf_kind_car_ne.
    (* f_equiv; f_equiv => ?; *) solve_proper_ho.
  Qed. *)
  Next Obligation.
    move=> n S K ρ m T1 T2 HT U1 U2 HU /=.
    (* have Hne: ∀ ρ, NonExpansive2 (sf_kind_sub K ρ) by apply sf_kind_sub_ne. *)
    f_equiv; f_equiv => ?; f_equiv.
    by apply sf_kind_sub_ne; f_equiv.
    (* apply Hne; by f_equiv. *)
  Qed.
  (* Next Obligation.
    iIntros "* #H !>" (arg) "#Harg".
    iApply (sf_kind_sub_refl with "(H Harg)").
  Qed. *)
  Next Obligation.
    iIntros "* #H1 #H2 !>" (arg) "#Harg".
    iApply (sf_kind_sub_trans with "(H1 Harg) (H2 Harg)").
  Qed.
  Next Obligation.
    iIntros "* /= #H !> * #Harg"; iApply (sf_kind_sub_quasi_refl_1 with "(H Harg)").
  Qed.
  Next Obligation.
    iIntros "* /= #H !> * #Harg"; iApply (sf_kind_sub_quasi_refl_2 with "(H Harg)").
  Qed.

  Definition sf_star : sf_kind Σ 0 := sf_kintv oBot oTop.

  Fixpoint s_kind_to_spine_s_kind {n} (K : s_kind Σ n) : spine_s_kind Σ n :=
    match K with
    | s_kintv L U => sp_s_kintv L U
    | s_kpi s K => sp_s_kpi s (s_kind_to_spine_s_kind K)
    end.

  Definition spine_s_kind_to_sf_kind {n} (K : spine_s_kind Σ n) : sf_kind Σ n :=
    vec_fold (sf_kintv (spine_L K) (spine_U K)) (@sf_kpi) n (spine_kargs K).
  Global Arguments spine_s_kind_to_sf_kind {_} !_.

  Fixpoint s_kind_to_sf_kind {n} (K : s_kind Σ n) : sf_kind Σ n :=
    match K with
    | s_kintv L U => sf_kintv L U
    | s_kpi s K => sf_kpi s (s_kind_to_sf_kind K)
    end.

  Definition oLam {n} (τ : oltyO Σ n) : oltyO Σ n.+1 :=
    Olty (λI args ρ, τ (vtail args) (vhead args .: ρ)).
    (* vuncurry (λ v, Olty (λ args ρ, τ args (v .: ρ))). *)
  Definition oTAppV {n} (T : oltyO Σ n.+1) w : olty Σ n :=
    Olty (λI args ρ, T (vcons w.[ρ] args) ρ).

  Lemma swap_oLam_oLater {n} (τ : olty Σ n) :
    oLater (oLam τ) ≡ oLam (oLater τ).
  Proof. done. Qed.

  Lemma swap_oTApp_oLater {n} (τ : olty Σ (S n)) v:
    oLater (oTAppV τ v) ≡ oTAppV (oLater τ) v.
  Proof. done. Qed.

End kinds_types.

Coercion s_kind_to_sf_kind : s_kind >-> sf_kind.

(** Kinded, indexed subtyping *)
Program Definition sstpkD `{!dlangG Σ} {n} i Γ T1 T2 (K : sf_kind Σ n) : iProp Σ :=
  □∀ ρ, s⟦Γ⟧*ρ → ▷^i K ρ (envApply T1 ρ) (envApply T2 ρ).
Notation "Γ s⊨ T1 <:[ i  ] T2 ∷ K" := (sstpkD i Γ T1 T2 K)
  (at level 74, i, T1, T2, K at next level).

Notation "Γ s⊨ T1 =[ i  ] T2 ∷ K" :=
  (Γ s⊨ T1 <:[ i  ] T2 ∷ K ∧ Γ s⊨ T2 <:[ i  ] T1 ∷ K)%I
  (at level 74, i, T1, T2, K at next level).

Notation "Γ s⊨ T ∷[ i  ] K" := (Γ s⊨ T <:[ i ] T ∷ K)
  (at level 74, T, K at next level).

Definition ssktp `{!dlangG Σ} {n} i Γ (K1 K2 : sf_kind Σ n) : iProp Σ :=
  □∀ ρ, s⟦Γ⟧*ρ → ∀ (T1 T2 : hoLtyO Σ n), ▷^i (K1 ρ T1 T2 → K2 ρ T1 T2).
Notation "Γ s⊨ K1 <∷[ i  ] K2" := (ssktp i Γ K1 K2)
  (at level 74, K1, K2 at next level).

(* XXX *)
Add Printing Constructor iPPred.
Section gen_lemmas.
  Context `{dlangG Σ} `{HswapProp: SwapPropI Σ}.

  Local Notation IntoPersistent' P := (IntoPersistent false P P).

  Global Instance sstpkD_persistent : IntoPersistent' (sstpkD (n := n) i Γ T1 T2 K) | 0 := _.
  (* Global Instance sktp_persistent `{!dlangG Σ} : IntoPersistent' (sktp (n := n) i Γ T K) | 0 := _. *)
  Global Instance ssktp_persistent : IntoPersistent' (ssktp (n := n) i Γ K1 K2) | 0 := _.
  Global Instance subtype_lty_persistent : IntoPersistent' (T1 ⊆@{Σ} T2) | 0 := _.

  Lemma ksubtyping_spec ρ i Γ T1 T2 :
    Γ s⊨ T1 <:[ i ] T2 ∷ sf_star -∗
    s⟦ Γ ⟧* ρ -∗
    ▷^i (oClose T1 ρ ⊆ oClose T2 ρ).
  Proof.
    iIntros "#Hsub #Hg" (v).
    iDestruct ("Hsub" $! ρ with "Hg") as "{Hsub} (_ & #Hsub &_)"; iNext i;
      iApply ("Hsub" $! v).
  Qed.

  Lemma ksubtyping_intro i Γ (T1 T2 : olty Σ 0) :
    (□∀ ρ, s⟦ Γ ⟧* ρ →
    ∀ v, ▷^i (oClose T1 ρ v → oClose T2 ρ v)) -∗
    Γ s⊨ T1 <:[ i ] T2 ∷ sf_star.
  Proof.
    iIntros "#Hsub !> * #Hg".
    iDestruct ("Hsub" with "Hg") as "{Hsub Hg} Hsub".
    iNext i; repeat iSplit;
      iIntros (v) "!>"; [iIntros "[]" | iApply "Hsub" | iIntros "_ //"].
  Qed.

  Lemma ksubtyping_intro_swap i Γ (T1 T2 : olty Σ 0) :
    (□∀ ρ, s⟦ Γ ⟧* ρ →
    ∀ v, ▷^i oClose T1 ρ v → ▷^i oClose T2 ρ v) -∗
    Γ s⊨ T1 <:[ i ] T2 ∷ sf_star.
  Proof using HswapProp.
    rewrite -ksubtyping_intro; iIntros "#Hsub !> * #Hg *".
    iApply (impl_laterN with "(Hsub Hg)").
  Qed.

  Lemma kinding_intro Γ i (L T U : olty Σ 0) :
    (□∀ ρ, s⟦ Γ ⟧* ρ →
    ▷^i (oClose L ρ ⊆ oClose T ρ ⊆ oClose U ρ)) -∗
    Γ s⊨ T ∷[ i ] sf_kintv L U.
  Proof.
    iIntros "#Hsub !>" (ρ). rewrite -sr_kintv_refl /sp_kintv /=. iApply "Hsub".
  Qed.

  (** * Prefixes: K for Kinding, KStp for kinded subtyping, Skd for subkinding. *)
  (* XXX: Prefixes: Rename elsewhere Sub to STyp *)
  Lemma sK_Sing Γ (T : olty Σ 0) i :
    Γ s⊨ T ∷[ i ] sf_kintv T T.
  Proof.
    rewrite -kinding_intro; iIntros "!>" (ρ) "_". by rewrite -subtype_refl.
  Qed.

  Lemma sKStp_Intv Γ (T1 T2 L U : olty Σ 0) i :
    Γ s⊨ T1 <:[i] T2 ∷ sf_kintv L U -∗
    Γ s⊨ T1 <:[i] T2 ∷ sf_kintv T1 T2.
  Proof.
    iIntros "#Hs !> * Hg"; iDestruct ("Hs" with "Hg") as "{Hs} (_ & $ & _)".
    by rewrite -!subtype_refl.
  Qed.

  (** Kind subsumption (for kinded subtyping). *)
  Lemma sKStp_Sub Γ {n} (T1 T2 : olty Σ n) (K1 K2 : sf_kind Σ n) i :
    Γ s⊨ T1 <:[ i ] T2 ∷ K1 -∗
    Γ s⊨ K1 <∷[ i ] K2 -∗
    Γ s⊨ T1 <:[ i ] T2 ∷ K2.
  Proof.
    iIntros "#H1 #Hsub !>" (ρ) "#Hg". iApply ("Hsub" with "Hg (H1 Hg)").
  Qed.

  (** Kind subsumption (for kinding). *)
  Lemma sK_Sub Γ {n} (T : olty Σ n) (K1 K2 : sf_kind Σ n) i :
    Γ s⊨ T ∷[ i ] K1 -∗
    Γ s⊨ K1 <∷[ i ] K2 -∗
    Γ s⊨ T ∷[ i ] K2.
  Proof. apply sKStp_Sub. Qed.

  Definition oShift {n} (T : oltyO Σ n) :=
    Olty (λ args ρ v, T args (stail ρ) v).
  Lemma oShift_eq {n} (T : oltyO Σ n) : oShift T ≡ shift T.
  Proof. move=>args ρ v /=. by rewrite (hoEnvD_weaken_one _ _ _ v). Qed.

  Lemma sKStp_Lam Γ {n} (K : sf_kind Σ n) S T1 T2 i :
    oLaterN i (oShift S) :: Γ s⊨ T1 <:[i] T2 ∷ K -∗
    Γ s⊨ oLam T1 <:[i] oLam T2 ∷ sf_kpi S K.
  Proof using HswapProp.
    iIntros "#HTK !> * #Hg * /=" (arg).
    rewrite -mlaterN_pers -impl_laterN.
    iIntros "!> Hs".
    iSpecialize ("HTK" $! (arg .: ρ) with "[$Hg $Hs]").
    by iApply (Proper_sfkind with "HTK").
  Qed.

  Lemma sK_Lam Γ {n} (K : sf_kind Σ n) S T i :
    oLaterN i (oShift S) :: Γ s⊨ T ∷[i] K -∗
    Γ s⊨ oLam T ∷[i] sf_kpi S K.
  Proof using HswapProp. apply sKStp_Lam. Qed.

    (* rewrite /vcurry /envApply/flip/oLam/Olty/vhead/vcons/=.
    by iApply "HTK".
    case: (oLam T).
    /iPPred_car/=.
    by iApply "HTK". *)
  (** * Subkinding *)
  Lemma sSkd_Intv (L1 L2 U1 U2 : olty Σ 0) Γ i :
    Γ s⊨ L2 <:[ i ] L1 ∷ sf_star -∗
    Γ s⊨ U1 <:[ i ] U2 ∷ sf_star -∗
    Γ s⊨ sf_kintv L1 U1 <∷[ i ] sf_kintv L2 U2.
  Proof.
    iIntros "#HsubL #HsubU !> * #Hg /=" (T1 T2).
    iPoseProof (ksubtyping_spec with "HsubL Hg") as "{HsubL} HsubL".
    iPoseProof (ksubtyping_spec with "HsubU Hg") as "{HsubU} HsubU".
    iNext i; iIntros "#(HsubL1 & $ & HsubU1)"; iSplit.
    iApply (subtype_trans with "HsubL HsubL1").
    iApply (subtype_trans with "HsubU1 HsubU").
  Qed.

  Lemma sSkd_Pi {n} (S1 S2 : olty Σ 0) (K1 K2 : sf_kind Σ n) Γ i :
    Γ s⊨ S2 <:[ i ] S1 ∷ sf_star -∗
    oLaterN i (oShift S2) :: Γ s⊨ K1 <∷[ i ] K2 -∗
    Γ s⊨ sf_kpi S1 K1 <∷[ i ] sf_kpi S2 K2.
  Proof using HswapProp.
    iIntros "#HsubS #HsubK !>" (ρ) "#Hg /=".
    iPoseProof (ksubtyping_spec with "HsubS Hg") as "{HsubS} HsubS".
    iAssert (□∀ arg : vl, let ρ' := arg .: ρ in
            ▷^i (oClose S2 ρ arg → ∀ T1 T2 : hoLtyO Σ n,
            K1 ρ' T1 T2 → K2 ρ' T1 T2))%I as
            "{HsubK} #HsubK". {
      setoid_rewrite <-mlaterN_impl.
      iIntros "!> * #HS2" (T1 T2); rewrite -mlaterN_impl; iIntros "HK1".
      iApply ("HsubK" $! (arg .: ρ) with "[$Hg $HS2] HK1").
    }
    iIntros (T1 T2); iNext i; iIntros "#HTK1 !> * #HS".
    iSpecialize ("HsubK" $! arg with "HS").
    iApply ("HsubK" with "(HTK1 (HsubS HS))").
  Qed.

  (** Reflexivity and transitivity of subkinding seem admissible, but let's
  prove them anyway, to show they hold regardless of extensions. *)
  Lemma sSkd_Refl {n} Γ i (K : sf_kind Σ n) :
    Γ s⊨ K <∷[ i ] K.
  Proof using HswapProp.
    rewrite /ssktp; setoid_rewrite <-(impl_laterN _).
    iIntros "!> * Hg * $".
  Qed.

  Lemma sSkd_Trans {n} Γ i (K1 K2 K3 : sf_kind Σ n) :
    Γ s⊨ K1 <∷[ i ] K2 -∗
    Γ s⊨ K2 <∷[ i ] K3 -∗
    Γ s⊨ K1 <∷[ i ] K3.
  Proof using HswapProp.
    iIntros "#Hs1 #Hs2 !> * #Hg *"; rewrite -impl_laterN; iIntros "#HK1".
    iApply ("Hs2" with "Hg (Hs1 Hg HK1)").
  Qed.

  (** * Kinded subtyping. *)

  Lemma sKStp_Refl Γ {n} T (K : sf_kind Σ n) i :
    Γ s⊨ T ∷[ i ] K -∗
    Γ s⊨ T <:[ i ] T ∷ K.
  Proof. done. Qed.

  (* XXX fixing ones in lty.v. *)
  Global Instance iPPred_car_ne n subj : Proper (dist n ==> (=) ==> dist n) (@iPPred_car subj Σ).
  Proof. by intros A A' HA w ? <-. Qed.
  Global Instance iPPred_car_proper subj : Proper ((≡) ==> (=) ==> (≡)) (@iPPred_car subj Σ).
  Proof. by intros A A' ? w ? <-. Qed.

  (* We can't actually write the right instance; this is just false for arbitrary persistent predicates.
    Instead, we must use Proper_sfkind, which is a setoid instance for a *pair* of projections.
   *)
  (* Global Instance iPPred_car_ne (subj : ofeT) n : Proper (dist n ==> (≡) ==> dist n) (@iPPred_car subj Σ).
  Proof. intros A A' HA w ? ?. apply (HA _). <-. Qed.
  Global Instance lty_car_proper subj : Proper ((≡) ==> (≡) ==> (≡)) (@iPPred_car subj Σ).
  Proof. by intros A A' ? w ? <-. Qed. *)

  Global Instance: Params (@sf_kind_sub) 4 := {}.
  (** XXX no ofe instance for sf_kind. *)
  Global Instance Proper_sstpkD n i :
    Proper ((≡) ==> (≡) ==> (≡) ==> (=) ==> (≡)) (sstpkD (Σ := Σ) (n := n) i).
  Proof.
    rewrite /sstpkD=> Γ1 Γ2 HΓ T1 T2 HT U1 U2 HU K ? <-.
    setoid_rewrite HΓ; properness; first done.
    by apply Proper_sfkind; f_equiv.
  Qed.
  Global Instance: Params (@sstpkD) 4 := {}.

  (* Replace by a Proper instance. *)
  (* Lemma sKStp_Refl_Aux {n} Γ T1 T2 (K : sf_kind Σ n) i :
    T1 ≡ T2 →
    Γ s⊨ T1 ∷[i] K -∗
    Γ s⊨ T1 <:[i] T2 ∷ K.
  Proof. intros ->. apply sKStp_Refl. Qed. *)

  Lemma sKEq_Refl {n} Γ T1 T2 (K : sf_kind Σ n) i :
    T1 ≡ T2 →
    Γ s⊨ T1 ∷[i] K -∗
    Γ s⊨ T1 =[i] T2 ∷ K.
  Proof.
    (* intros <-; iIntros "$".  *)
    iIntros (Heq) "#H"; by iSplit; iApply (Proper_sstpkD with "H").
  Qed.

  Lemma sKEq_Eta {n} Γ S T (K : sf_kind Σ n) i :
    Γ s⊨ T ∷[i] sf_kpi S K -∗
    Γ s⊨ T =[i] oLam (oTAppV (oShift T) (ids 0)) ∷ sf_kpi S K.
  Proof.
    iApply sKEq_Refl => + ρ v /=; apply: vec_S_inv => w args.
    autosubst.
  Qed.

  Lemma sKStp_Trans Γ {n} T1 T2 T3 (K : s_kind Σ n) i :
    Γ s⊨ T1 <:[ i ] T2 ∷ K -∗
    Γ s⊨ T2 <:[ i ] T3 ∷ K -∗
    Γ s⊨ T1 <:[ i ] T3 ∷ K.
  Proof.
    iIntros "#Hs1 #Hs2 !> * #Hg".
    iApply (sf_kind_sub_trans with "(Hs1 Hg) (Hs2 Hg)").
  Qed.

  (* Notation "" := sf_star. *)
  (* Notation "L  U" := (sf_kintv L U) (at level 70). *)

  Lemma sKStp_Top Γ (T : olty Σ 0) i :
    Γ s⊨ T <:[ i ] ⊤ ∷ sf_star.
  Proof. rewrite -ksubtyping_intro. iIntros "!> * _ * !> _ //". Qed.
  Lemma sKStp_Bot Γ (T : olty Σ 0) i :
    Γ s⊨ ⊥ <:[ i ] T ∷ sf_star.
  Proof. rewrite -ksubtyping_intro; iIntros "!> * _ * !> []". Qed.

  (* <:-..-U *)
  Lemma sKStp_IntvU Γ T L U i :
    Γ s⊨ T ∷[ i ] sf_kintv L U -∗
    Γ s⊨ T <:[ i ] U ∷ sf_star.
  Proof.
    rewrite -ksubtyping_intro; iIntros "#HK !> * Hg *".
    iDestruct ("HK" with "Hg") as "[_ [_ Hsub]]".
    iNext i; iApply "Hsub".
  Qed.

  (* <:-..-L *)
  Lemma sKStp_IntvL Γ T L U i :
    Γ s⊨ T ∷[ i ] sf_kintv L U -∗
    Γ s⊨ L <:[ i ] T ∷ sf_star.
  Proof.
    rewrite -ksubtyping_intro; iIntros "#HK !> * Hg *".
    iDestruct ("HK" with "Hg") as "[Hsub _]".
    iNext i; iApply "Hsub".
  Qed.
End gen_lemmas.

End HoSemTypes.

Module HkDot.
Import dot_lty unary_lr lr_lemmasNoBinding typeExtractionSem.
Include HoSemTypes VlSorts dlang_inst dot_lty.
Implicit Types
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : var → vl) (l : label).

Section dot_types.
  Context `{dlangG Σ} `{HswapProp: SwapPropI Σ}.

  (* XXX move to lty, generalize, name, etc. We can define something like kSub for arbitrary iPred, derive
  kSubstOne and oShift, prove that they correspond to shift and substitution, lift them over reader monads...
  and only finally lift that over sf_kind. *)
  (* XXX Name. *)
  Program Definition kSub {n} (f : env → env) (K : sf_kind Σ n) : sf_kind Σ n :=
    SfKind (λI ρ, K (f ρ)) _ _ _ _.
  Next Obligation.
    move=> n K v ρ m T1 T2 HT U1 U2 HU /=; exact: sf_kind_sub_ne.
  Qed.
  Next Obligation. intros; simpl; exact: sf_kind_sub_trans. Qed.
  Next Obligation. intros; simpl; exact: sf_kind_sub_quasi_refl_1. Qed.
  Next Obligation. intros; simpl; exact: sf_kind_sub_quasi_refl_2. Qed.

  Global Instance hsubst_sf_kind {n}: HSubst vl (sf_kind Σ n) :=
    λ σ K, kSub (λ ρ, (σ >> ρ)) K.
  Definition kSubstOne {n} v (K : sf_kind Σ n) : sf_kind Σ n :=
    kSub (λ ρ, v.[ρ] .: ρ) K.
  Lemma kSubstOne_eq {n} (K : sf_kind Σ n) v ρ : sf_kind_sub K.|[v/] ρ = kSubstOne v K ρ.
  Proof. by rewrite /sf_kind_sub/= subst_swap_base. Qed.

  Lemma sKStp_AppV Γ {n} (K : sf_kind Σ n) S T1 T2 i v :
    Γ s⊨ T1 <:[i] T2 ∷ sf_kpi S K -∗
    Γ s⊨p pv v : S, i -∗
    Γ s⊨ oTAppV T1 v <:[i] oTAppV T2 v ∷ K.|[v/].
  Proof.
    iIntros "#HTK #Hv !> * #Hg"; rewrite kSubstOne_eq /=.
    iSpecialize ("HTK" with "Hg"); iSpecialize ("Hv" with "Hg"); iNext i.
    rewrite path_wp_pv_eq /=.
    by iApply (Proper_sfkind with "(HTK Hv)").
  Qed.

  Lemma sK_AppV Γ {n} (K : sf_kind Σ n) S T i v :
    Γ s⊨ T ∷[i] sf_kpi S K -∗
    Γ s⊨p pv v : S, i -∗
    Γ s⊨ oTAppV T v ∷[i] K.|[v/].
  Proof. apply sKStp_AppV. Qed.

  Lemma sKEq_BetaV {n} Γ S T (K : sf_kind Σ n) i v :
    Γ s⊨p pv v : S, i -∗
    oLaterN i (oShift S) :: Γ s⊨ T ∷[i] K -∗
    Γ s⊨ oTAppV (oLam T) v =[i] T.|[v/] ∷ K.|[v/].
  Proof using HswapProp.
    iIntros "#Hp #HK"; iApply sKEq_Refl.
    by move => args ρ w; rewrite /= /hsubst /hsubst_hoEnvD/=; autosubst.
    iIntros "!> * #Hg"; rewrite sK_Lam kSubstOne_eq /=.
    iSpecialize ("Hp" with "Hg"); iSpecialize ("HK" with "Hg"); iNext i.
    rewrite path_wp_pv_eq. by iApply (Proper_sfkind' with "(HK Hp)").
  Qed.

  Definition oTApp {n} (T : oltyO Σ n.+1) (p : path) : oltyO Σ n :=
    Olty (λ args ρ v, path_wp p.|[ρ] (λ w, T (vcons w args) ρ v)).
  Lemma oTApp_pv {n} (T : oltyO Σ n.+1) w :
    oTApp T (pv w) ≡ oTAppV T w .
  Proof. intros ???. by rewrite /= path_wp_pv_eq. Qed.

  Global Instance: Params (@sf_kind_sub) 4 := {}.
  (** XXX Copy-paste of sKStp_AppV, plus hacks for missing Proper instances I guess? *)
  Lemma sKStp_App Γ {n} (K : sf_kind Σ n) S T1 T2 i v :
    Γ s⊨ T1 <:[i] T2 ∷ sf_kpi S K -∗
    Γ s⊨p pv v : S, i -∗
    Γ s⊨ oTApp T1 (pv v) <:[i] oTApp T2 (pv v) ∷ K.|[v/].
  Proof.
    iIntros "#HTK #Hv !> * #Hg". rewrite kSubstOne_eq /=.
    iSpecialize ("HTK" with "Hg"); iSpecialize ("Hv" with "Hg"); iNext i.
    rewrite path_wp_pv_eq /=.
    iSpecialize ("HTK" with "Hv").
    (* Argh. *)
    (* About sf_kind_sub. *)
    (* Set Typeclasses Debug. *)
    (* iEval rewrite {1}(oTApp_pv T). *)
    (* Timeout 1 iEval rewrite oTApp_pv. *)
    iApply (Proper_sfkind with "HTK"); by rewrite oTApp_pv.
    (* Time by rewrite oTApp_pv. *)
    (* Argh. *)
    (* iApply ("HTK"). *)
    (* by rewrite (oTApp_pv _ _ _ _ _). *)
    (* by rewrite /= path_wp_pv_eq. *)
  Qed.

    (* rewrite /oTAppV/envApply/flip.
    iApply (Proper_sfkind).
    cbn.

    iApply (Proper_sfkind with "HTK").
    iS
    rewrite -mlaterN_pers -impl_laterN.
    iIntros "!> Hs".
    iSpecialize ("HTK" $! (arg .: ρ) with "[$Hg $Hs]").
    by iApply (Proper_sfkind with "HTK").
  Qed. *)

  (* XXX argh. *)
  (* Definition kind_path_subst {n} p q (K1 K2 : sf_kind Σ n) : iProp Σ :=
    ∀ (H : alias_paths p q) ρ T1 T2,
    K1 ρ T1 T2 ≡ K2 ρ T1 T2 .

  Lemma sKStp_App Γ {n} (K1 K2 : sf_kind Σ n) S T i p :
    Γ s⊨ T ∷[i] sf_kpi S K1 -∗
    Γ s⊨p p : S, i -∗
    Γ s⊨ oTAppV T v ∷[i] K2.
  Proof.
    iIntros "#HTK #Hv !> * #Hg".
    rewrite kSubstOne_eq /=.
    iSpecialize ("HTK" with "Hg"); iSpecialize ("Hv" with "Hg").
    rewrite path_wp_pv_eq /=; iNext i.
    iSpecialize ("HTK" with "Hv").
    (* iEval rewrite /sf_kind_sub/=.
    iApply ("HTK"). *)
    by iApply (Proper_sfkind with "HTK").
  Qed. *)



  Lemma sstpkD_star_to_sstp Γ i T1 T2 :
    Γ s⊨ T1 <:[ i ] T2 ∷ sf_star ⊢ Γ s⊨ T1 , i <: T2 , i.
  Proof.
    iIntros "#Hsub !>" (ρ v) "#Hg".
    iDestruct (ksubtyping_spec with "Hsub Hg") as "{Hsub Hg} Hsub".
    rewrite -laterN_impl. iNext i. iApply ("Hsub" $! v).
  Qed.

  Lemma sstpkD_star_eq_sstp Γ i T1 T2 :
    Γ s⊨ T1 <:[ i ] T2 ∷ sf_star ⊣⊢ Γ s⊨ T1 , i <: T2 , i.
  Proof using HswapProp.
    iSplit; first iApply sstpkD_star_to_sstp.
    rewrite -ksubtyping_intro_swap /=. iIntros "#Hsub !> * Hg *".
    iApply ("Hsub" with "Hg").
  Qed.


  Notation hoLty_car τ := (λ args v, lty_car (τ args) v).
  Notation HoLty φ := (λ args, Lty (λI v, φ args v)).
  Definition packHoLtyO {Σ n} (φ : hoD Σ n) : hoLtyO Σ n := HoLty (λI args v, ▷ □ φ args v).

  Definition oLDTMemK {n} l (K : sf_kind Σ n) : ldltyO Σ := mkLDlty (Some l) (λI ρ d,
    ∃ (ψ : hoD Σ n), d ↗n[ n ] ψ ∧ K ρ (packHoLtyO ψ) (packHoLtyO ψ)).
  Definition oLDTMemSpec l (L U : olty Σ 0) : ldltyO Σ :=
    oLDTMemK l (sf_kintv (oLater L) (oLater U)).

  (** [cTMem] and [cVMem] are full [clty]. *)
  Definition cTMemK {n} l (K : sf_kind Σ n) : clty Σ := ldlty2clty (oLDTMemK l K).
  (** Here [n]'s argument to oSel should be explicit. *)
  Global Arguments oSel {_ _} n p l args ρ : rename.

  Lemma sKStp_TMem {n} Γ l (K1 K2 : s_kind Σ n) i :
    Γ s⊨ K1 <∷[ i ] K2 -∗
    Γ s⊨ cTMemK l K1 <:[ i ] cTMemK l K2 ∷ sf_star.
  Proof using HswapProp.
    rewrite -ksubtyping_intro_swap.
    iIntros "#HK !> * #Hg * /=".
    iDestruct 1 as (d) "[Hld Hφ]"; iExists d; iFrame "Hld".
    iDestruct "Hφ" as (φ) "[Hlφ #HK1]"; iExists φ; iFrame "Hlφ".
    iApply ("HK" with "Hg HK1").
  Qed.

  (** * Kinding *)
  Lemma sK_Star Γ (T : olty Σ 0) i :
    Γ s⊨ T ∷[ i ] sf_star.
  Proof using HswapProp.
    iApply sK_Sub. iApply sK_Sing. iApply sSkd_Intv; rewrite sstpkD_star_eq_sstp.
    by iApply sBot_Sub.
    by iApply sSub_Top.
  Qed.

  (** Generalization of [sD_Typ_Abs]. *)
  Lemma sD_TypK_Abs {Γ n} T (K : sf_kind Σ n) s σ l:
    Γ s⊨ oLater T ∷[ 0 ] K -∗
    s ↝[ σ ] T -∗
    Γ s⊨ { l := dtysem σ s } : cTMemK l K.
  Proof.
    iIntros "#HTK"; iDestruct 1 as (φ Hγφ) "#Hγ".
    iIntros "/= !>" (ρ Hpid) "Hg"; iSplit; first done.
    iExists (hoEnvD_inst (σ.|[ρ]) φ); iSplit.
    by iApply (dm_to_type_intro with "Hγ").
    iApply (Proper_sfkind' with "(HTK Hg)") => args v /=.
    by rewrite -(Hγφ args ρ v) make_intuitionistically.
  Qed.
  (* Lemma lift_olty_eq subj {τ1 τ2 : iPPred subj Σ} :
    (sbi_internal_eq (A := subj -d> _) (iPPred_car τ1) (iPPred_car τ2)) ⊢@{iPropI Σ} τ1 ≡ τ2.
  Proof.
  Admitted. *)
    (* iIntros "H".
    iApply prop_ext_2.
    rewrite equiv_internal_eq.
    iApply internal_eq_rewrite. ∗.
  apply. Qed. *)

  Lemma sfkind_respects {n} (K : sf_kind Σ n) ρ (T1 T2 : hoLtyO Σ n) :
    (∀ args v, T1 args v ↔ T2 args v) ⊢@{iPropI Σ} K ρ T1 T1 -∗ K ρ T2 T2.
  Proof.
    (* repeat setoid_rewrite <-bi.discrete_fun_equivI.  *)
  Admitted.

  (* Lemma sK_Sel {Γ n} l (K : s_kind Σ n) v i : *)
  Lemma sK_Sel {Γ n} l (K : sf_kind Σ n) v i :
    Γ s⊨p pv v : cTMemK l K, i -∗
    Γ s⊨ oSel n (pv v) l ∷[i] K.
  Proof.
    iIntros "#Hp !> * #Hg"; iSpecialize ("Hp" with "Hg"); iNext i.
    rewrite /= path_wp_pv_eq /=; iDestruct "Hp" as (d Hl ψ) "[Hl HK]".
    iApply (sfkind_respects with "[] HK"); iIntros (args w).
    rewrite /= path_wp_pv_eq.
    iSplit; first by iIntros "H"; iExists ψ, d; iFrame (Hl) "Hl".
    iDestruct 1 as (ψ' ?d Hl') "[Hl' Hw]"; objLookupDet.
    iDestruct (dm_to_type_agree args w with "Hl Hl'") as "Hag".
    iNext. by iRewrite "Hag".
  Qed.

End dot_types.
End HkDot.
