(* (* Must be loaded first, so that other modules can reset some flags. *)
Require Import Equations.Equations. *)
From Coq Require FunctionalExtensionality.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
From D Require Import iris_prelude.
From D Require Import saved_interp_dep asubst_intf asubst_base dlang lty.
From D Require Import swap_later_impl.
From D.Dot.lr Require dot_lty unary_lr lr_lemmasNoBinding.

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
Notation "X ⊆ Y ⊆ Z" := (X ⊆ Y ∧ Y ⊆ Z)%I : bi_scope.
Notation "X ⊆ Y ⊆ Z ⊆ W" := (X ⊆ Y ∧ Y ⊆ Z ∧ Z ⊆ W)%I (at level 70, Y, Z at next level) : bi_scope.

(** Semantic Full Kind. *)
Record sf_kind {Σ n} := SfKind {
  sf_kind_car :> sp_kind Σ n;
  sf_kind_sub : sr_kind Σ n;
  sf_kind_car_ne ρ :> NonExpansive (sf_kind_car ρ);
  sf_kind_sub_ne ρ :> NonExpansive2 (sf_kind_sub ρ);
}.
Global Arguments sf_kind : clear implicits.
Global Arguments sf_kind_car : simpl never.
Global Arguments sf_kind_sub : simpl never.
Global Arguments SfKind {_ _} _ _ _ _.

Global Instance Proper_sfkind {Σ n} (K : sf_kind Σ n) ρ :
  Proper ((≡) ==> (≡)) (K ρ).
Proof.
  move=> T1 T2 HT.
  apply equiv_dist => m.
  apply sf_kind_car_ne, equiv_dist, HT.
Qed.
Global Instance Proper_sfkind_A {Σ n} (K : sf_kind Σ n) ρ :
  Proper (pointwise_relation _ (≡) ==> (≡)) (K ρ).
Proof. move=> T1 T2 HT; apply Proper_sfkind => v; by rewrite (HT v). Qed.

Global Instance vcurry_ne vl n A m : Proper (dist m ==> (=) ==> dist m) (@vcurry vl n A).
Proof. solve_proper_ho. Qed.

Section kinds_types.
  Context {Σ}.

  Definition sp_kintv (L U : olty Σ 0) : spine_s_kind Σ 0 := SpineSK vnil L U.
  Definition sp_kpi {n} (S : olty Σ 0) (K : spine_s_kind Σ n) : spine_s_kind Σ n.+1 :=
    SpineSK (vcons S (spine_kargs K)) (spine_L K) (spine_U K).

  Program Definition sf_kintv (L U : olty Σ 0) : sf_kind Σ 0 :=
    SfKind
      (SpKind (λI ρ φ,
        oClose L ρ ⊆ oClose φ ⊆ oClose U ρ))
      (SrKind (λI ρ φ1 φ2,
        oClose L ρ ⊆ oClose φ1 ⊆ oClose φ2 ⊆ oClose U ρ)) _ _.
  Solve All Obligations with solve_proper_ho.

  Program Definition sf_kpi {n} (S : olty Σ 0) (K : sf_kind Σ n) : sf_kind Σ n.+1 :=
    SfKind
      (SpKind (λI ρ φ,
        □∀ arg, S vnil ρ arg →
        sf_kind_car K (arg .: ρ) (vcurry φ arg)))
      (SrKind (λI ρ φ1 φ2,
        □∀ arg, S vnil ρ arg →
        sf_kind_sub K (arg .: ρ) (vcurry φ1 arg) (vcurry φ2 arg))) _ _.
  Next Obligation.
    move=> n S K ρ m T1 T2 HT /=.
    have ?: ∀ ρ, NonExpansive (sf_kind_car K ρ) by apply sf_kind_car_ne.
    (* f_equiv; f_equiv => ?; *) solve_proper_ho.
  Qed.
  Next Obligation.
    move=> n S K ρ m T1 T2 HT U1 U2 HU /=.
    (* have Hne: ∀ ρ, NonExpansive2 (sf_kind_sub K ρ) by apply sf_kind_sub_ne. *)
    f_equiv; f_equiv => ?; f_equiv.
    by apply sf_kind_sub_ne; f_equiv.
    (* apply Hne; by f_equiv. *)
  Qed.

  Definition sf_star : sf_kind Σ 0 := sf_kintv oBot oTop.

  Fixpoint s_kind_to_spine_s_kind {n} (K : s_kind Σ n) : spine_s_kind Σ n :=
    match K with
    | s_kintv L U => sp_kintv L U
    | s_kpi s K => sp_kpi s (s_kind_to_spine_s_kind K)
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
  □∀ ρ, s⟦Γ⟧*ρ → ▷^i sf_kind_sub K ρ (envApply T1 ρ) (envApply T2 ρ).
Notation "Γ s⊨ T1 <:[ i  ] T2 ∷ K" := (sstpkD i Γ T1 T2 K)
  (at level 74, i, T1, T2, K at next level).

Definition sktp `{!dlangG Σ} {n} i Γ T (K : sf_kind Σ n) : iProp Σ :=
  □∀ ρ, s⟦Γ⟧*ρ → ▷^i K ρ (envApply T ρ).
Notation "Γ s⊨ T ∷[ i  ] K" := (sktp i Γ T K)
  (at level 74, T, K at next level).
Definition ssktp `{!dlangG Σ} {n} i Γ (K1 K2 : sf_kind Σ n) : iProp Σ :=
  □∀ ρ, s⟦Γ⟧*ρ → ∀ (T : oltyO Σ n), ▷^i (K1 ρ (envApply T ρ) → K2 ρ (envApply T ρ)).
Notation "Γ s⊨ K1 <∷[ i  ] K2" := (ssktp i Γ K1 K2)
  (at level 74, K1, K2 at next level).

Section gen_lemmas.
  Context `{dlangG Σ} `{HswapProp: SwapPropI Σ}.

  Lemma s_kind_refl {n} (K : s_kind Σ n) T (ρ : env) :
    K ρ T -∗ sf_kind_sub K ρ T T.
  Proof.
    elim: n ρ K T => [|n IHn] ρ; cbn.
    - move E: 0 => n K T. destruct K as [L U|] eqn:?; simplify_eq.
      by iIntros "($&$) !>" (v) "$".
    - move E: n.+1 => m K T.
      (* case E': K T E => [|m S K'].
      case: K T E. *)
      destruct K as [|m S K'] eqn:?; simplify_eq/=.
      iIntros "#H !>" (arg) "#Harg".
      iApply (IHn with "(H Harg)").
  Qed.

  Lemma subtype_trans {T1} T2 {T3} :
    T1 ⊆ T2 ⊢@{iPropI Σ} T2 ⊆ T3 -∗ T1 ⊆ T3.
  Proof.
    iIntros "#Hs1 #Hs2 !>" (v) "#HT1".
    iApply ("Hs2" with "(Hs1 HT1)").
  Qed.

  Lemma s_kind_trans {n} (K : s_kind Σ n) T1 T2 T3 (ρ : env) :
    sf_kind_sub K ρ T1 T2 -∗
    sf_kind_sub K ρ T2 T3 -∗
    sf_kind_sub K ρ T1 T3.
  Proof.
    elim: n ρ K T1 T2 T3 => [|n IHn] ρ; cbn.
    - move E: 0 => n K T1 T2 T3. destruct K as [L U|] eqn:?; simplify_eq.
      iIntros "($&HLT1&_) (_ & HT2T3 & $)".
      iApply (subtype_trans (oClose T2) with "HLT1 HT2T3").
    - move E: n.+1 => m K T1 T2 T3.
      destruct K as [|m S K'] eqn:?; simplify_eq/=.
      iIntros "#H1 #H2 !>" (arg) "#Harg".
      iApply (IHn with "(H1 Harg) (H2 Harg)").
  Qed.

  Local Notation IntoPersistent' P := (IntoPersistent false P P).

  Global Instance sstpkD_persistent `{!dlangG Σ} : IntoPersistent' (sstpkD (n := n) i Γ T1 T2 K) | 0 := _.
  Global Instance sktp_persistent `{!dlangG Σ} : IntoPersistent' (sktp (n := n) i Γ T K) | 0 := _.
  Global Instance ssktp_persistent `{!dlangG Σ} : IntoPersistent' (ssktp (n := n) i Γ K1 K2) | 0 := _.

  Lemma ksubtyping_spec ρ i Γ T1 T2 :
    Γ s⊨ T1 <:[ i ] T2 ∷ sf_star -∗
    s⟦ Γ ⟧* ρ -∗
    ▷^i (∀ v, oClose T1 ρ v → oClose T2 ρ v).
  Proof.
    iIntros "#Hsub #Hg" (v).
    iDestruct ("Hsub" $! ρ with "Hg") as "{Hsub} (_ & #Hsub &_)"; iNext i;
      iApply ("Hsub" $! v).
  Qed.

  Lemma sK_Sing Γ (T : olty Σ 0) i :
    Γ s⊨ T ∷[ i ] sf_kintv T T.
  Proof. iIntros "!>" (ρ) "#Hg /="; iSplit; iIntros "!> !>" (v) "$". Qed.

  Lemma sK_KSub Γ {n} (T : olty Σ n) (K1 K2 : sf_kind Σ n) i :
    Γ s⊨ T ∷[ i ] K1 -∗
    Γ s⊨ K1 <∷[ i ] K2 -∗
    Γ s⊨ T ∷[ i ] K2.
  Proof.
    iIntros "#H1 #Hsub !>" (ρ) "#Hg".
    iApply ("Hsub" with "Hg (H1 Hg)").
  Qed.

  Definition oShift {n} (T : oltyO Σ n) :=
    Olty (λ args ρ v, T args (stail ρ) v).

  (** * Subkinding *)

  Lemma sKSub_Intv (L1 L2 U1 U2 : olty Σ 0) Γ i :
    Γ s⊨ L2 <:[ i ] L1 ∷ sf_star -∗
    Γ s⊨ U1 <:[ i ] U2 ∷ sf_star -∗
    Γ s⊨ sf_kintv L1 U1 <∷[ i ] sf_kintv L2 U2.
  Proof.
    iIntros "#HsubL #HsubU !>" (ρ) "#Hg". iIntros (T).
    iPoseProof (ksubtyping_spec with "HsubL Hg") as "{HsubL} HsubL".
    iPoseProof (ksubtyping_spec with "HsubU Hg") as "{HsubU} HsubU".
    iNext i.
    rewrite /sf_kind_sub/= /subtype_lty.
    iIntros "#[#HsubL1 #HsubU1] /=".
    iSplit; iIntros (v) "!> #H".
    by iApply ("HsubL1" with "(HsubL H)").
    by iApply ("HsubU" with "(HsubU1 H)").
  Qed.

  Lemma sKSub_Pi {n} (S1 S2 : olty Σ 0) (K1 K2 : sf_kind Σ n) Γ i :
    Γ s⊨ S2 <:[ i ] S1 ∷ sf_star -∗
    oLaterN i (shift S2) :: Γ s⊨ K1 <∷[ i ] K2 -∗
    Γ s⊨ sf_kpi S1 K1 <∷[ i ] sf_kpi S2 K2.
  Proof using HswapProp.
    iIntros "#HsubS #HsubK !>" (ρ) "#Hg /=".
    iPoseProof (ksubtyping_spec with "HsubS Hg") as "{HsubS} HsubS".
    iAssert (□∀ arg : vl, let ρ' := arg .: ρ in
            ▷^i (oClose S2 ρ arg → ∀ T : olty Σ n,
            K1 ρ' (envApply T ρ') → K2 ρ' (envApply T ρ')))%I as
            "{HsubK} #HsubK". {
      setoid_rewrite <-mlaterN_impl.
      iIntros "!>" (arg) "HS2"; iIntros (T).
      rewrite -mlaterN_impl.
      iIntros "HK1".
      iApply ("HsubK" $! (arg .: ρ) with "[$Hg HS2] HK1").
      iApply (hoEnvD_weaken_one S2 _ (_ .: _) _ with "HS2").
    }
    iIntros (T); iNext i.
    iIntros "#HTK1 !>" (arg) "#HS".
    iSpecialize ("HsubK" $! arg with "HS").
    (* iSpecialize ("HsubK" $! !!(shift (vcurry T arg)) with "[]"). {
      iApply (Proper_sfkind with "(HTK1 (HsubS HS))") => args v /=.
      by rewrite (hoEnvD_weaken_one (vcurry T arg) args (arg .: ρ) v).
    } *)
    iSpecialize ("HsubK" $! (oShift (vcurry T arg)) with "[]"). {
      by iApply (Proper_sfkind with "(HTK1 (HsubS HS))").
    }
    by iApply (Proper_sfkind with "HsubK").
  Qed.

  (** Reflexivity and transitivity of subkinding are admissible. *)

  (** * Kinded subtyping. *)
  Lemma ksubtyping_intro i Γ (T1 T2 : olty Σ 0) :
    (□∀ ρ, s⟦ Γ ⟧* ρ -∗
    ▷^i (∀ v, oClose T1 ρ v → oClose T2 ρ v)) -∗
    Γ s⊨ T1 <:[ i ] T2 ∷ sf_star.
  Proof.
    iIntros "#Hsub !> * #Hg".
    iDestruct ("Hsub" with "Hg") as "{Hsub Hg} Hsub"; iFrame "Hsub"; iClear "#".
    iNext i; iSplit;
      iIntros (v); [iIntros "!> []" | iIntros "!> _ //"].
  Qed.

  Lemma sSubK_Refl Γ {n} T (K : s_kind Σ n) i :
    Γ s⊨ T ∷[ i ] K -∗
    Γ s⊨ T <:[ i ] T ∷ K.
  Proof.
    iIntros "#HK !>". iIntros (ρ) "#Hg".
    iApply (s_kind_refl with "(HK Hg)").
  Qed.
End gen_lemmas.

End HoSemTypes.

Module HkDot.
Import dot_lty unary_lr lr_lemmasNoBinding.
Include HoSemTypes VlSorts dlang_inst dot_lty.
Implicit Types
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : var → vl) (l : label).

Section dot_types.
  Context `{dlangG Σ} `{HswapProp: SwapPropI Σ}.

  Lemma sstpkD_star_to_sstp Γ i T1 T2 :
    Γ s⊨ T1 <:[ i ] T2 ∷ sf_star ⊢ Γ s⊨ T1 , i <: T2 , i.
  Proof.
    iIntros "#Hsub !>" (ρ v) "#Hg".
    iDestruct (ksubtyping_spec with "Hsub Hg") as "{Hsub Hg} Hsub".
    rewrite -laterN_impl. iApply ("Hsub" $! v).
  Qed.

  Lemma sstpkD_star_eq_sstp Γ i T1 T2 :
    Γ s⊨ T1 <:[ i ] T2 ∷ sf_star ⊣⊢ Γ s⊨ T1 , i <: T2 , i.
  Proof using HswapProp.
    iSplit; first iApply sstpkD_star_to_sstp.
    rewrite -ksubtyping_intro; iIntros "#Hsub !> * Hg" (v).
    rewrite -impl_laterN.
    iApply ("Hsub" $! ρ v with "Hg").
  Qed.

  Definition oTApp {n} (T : oltyO Σ n.+1) (p : path) : olty Σ n :=
    Olty (λ args ρ v, path_wp p.|[ρ] (λ w, T (vcons w args) ρ v)).
  Lemma oTApp_pv {n} (T : oltyO Σ n.+1) w args ρ v :
    oTApp T (pv w) args ρ v ≡ oTAppV T w args ρ v.
  Proof. by rewrite /= path_wp_pv_eq. Qed.

  (* [K]'s argument must ignore [ρ]. Patch the definition of sp_kind instead. *)
  Notation HoLty φ := (λ args, Lty (λI v, φ args v)).
  Definition packHoLtyO {Σ n} (φ : hoD Σ n) : hoLtyO Σ n := HoLty (λI args v, □ ▷ φ args v).

  Definition oLDTMemK {n} l (K : sf_kind Σ n) : ldltyO Σ := mkLDlty (Some l) (λI ρ d,
    ∃ (ψ : hoD Σ n), d ↗n[ n ] ψ ∧ K ρ (packHoLtyO ψ)).
  Definition oLDTMemSpec l (L U : olty Σ 0) : ldltyO Σ :=
    oLDTMemK l (sf_kintv (oLater L) (oLater U)).

  (** [cTMem] and [cVMem] are full [clty]. *)
  Definition cTMemK {n} l (K : sf_kind Σ n) : clty Σ := ldlty2clty (oLDTMemK l K).
  (** Here [n]'s argument to oSel should be explicit. *)
  Global Arguments oSel {_ _} n p l args ρ : rename.

  (** * Kinding *)
  Lemma sK_Star Γ (T : olty Σ 0) i :
    Γ s⊨ T ∷[ i ] sf_star.
  Proof using HswapProp.
    iApply sK_KSub. iApply sK_Sing. iApply sKSub_Intv; rewrite sstpkD_star_eq_sstp.
    by iApply sBot_Sub.
    by iApply sSub_Top.
  Qed.
End dot_types.
End HkDot.
