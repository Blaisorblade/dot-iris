(** ** Semantic types, judgments, etc.
As usual in Iris, semantic types are persistent Iris predicates on values.
Since D* syntactic types can contain variables ranging on values, semantic types take a value substitution as argument.
Using Autosubst 1, we define substitution on semantic types by precomposition:
[ τ.|[s] = λ ρ, τ (ρ >> s) ].
*)
From D Require Import iris_prelude asubst_base asubst_intf dlang.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import language.
From D.pure_program_logic Require Import lifting adequacy.

From Coq Require ProofIrrelevance FunctionalExtensionality.

Module Type OLty (Import VS: VlSortsFullSig) (Import LVS : LiftWp VS).

Section olty_limit_preserving.
  Context `{Σ : gFunctors} {i : nat}.

  Definition hoEnvD_persistent (A : hoEnvD Σ i) := ∀ args ρ w, Persistent (A args ρ w).

  Instance: LimitPreserving hoEnvD_persistent.
  Proof.
    apply limit_preserving_forall=> args;
    apply limit_preserving_forall=> ρ; apply limit_preserving_forall=> w.
    apply bi.limit_preserving_Persistent => n f g Heq. exact: Heq.
  Qed.

  Definition restrict A := hoEnvD_persistent A.
  Global Instance: LimitPreserving restrict := _.
End olty_limit_preserving.

(**
"Open Logical TYpes": persistent Iris predicates over environments
and values. Adapted from
https://gitlab.mpi-sws.org/iris/examples/blob/d4f4153920ea82617c7222aeeb00b6710d51ee03/theories/logrel_heaplang/ltyping.v#L5. *)
Record olty Σ i := Olty {
  olty_car :> vec vl i → (var → vl) → vl → iProp Σ;
  olty_persistent args ρ v : Persistent (olty_car args ρ v);
}.
Global Arguments Olty {_ _} _%I {_}.
Global Arguments olty_car {_ _} _ _ _ _: simpl never.
Bind Scope olty_scope with olty.
Delimit Scope olty_scope with T.
Global Existing Instance olty_persistent.

(* Different from normal TyInterp. Better? *)
Class OTyInterp (ty : nat → Type) Σ :=
  oty_interp : ∀ {i}, ty i → olty Σ i.
(* Forces inserting coercions to -d>. *)
Notation oApp := (olty_car : olty _ _ → hoEnvD _ _).

Local Definition testCoerce `(τ : olty Σ 0) := vclose (oApp τ).

Section olty_ofe.
  Context `{Σ : gFunctors} {i : nat}.
  Implicit Types (φ : hoEnvD Σ i) (τ : olty Σ i).

  Instance olty_equiv : Equiv (olty Σ i) := λ A B, oApp A ≡ B.
  Instance olty_dist : Dist (olty Σ i) := λ n A B, oApp A ≡{n}≡ B.
  Lemma olty_ofe_mixin : OfeMixin (olty Σ i).
  Proof. by apply (iso_ofe_mixin oApp). Qed.
  Canonical Structure oltyO := OfeT (olty Σ i) olty_ofe_mixin.

  (* Only needed to define Olty using Iris fixpoints (e.g. for normal recursive types). *)
  Global Instance olty_cofe : Cofe oltyO.
  Proof.
    apply (iso_cofe_subtype' restrict Olty olty_car) => //.
    - by move => [].
    - apply _.
  Qed.

  Global Program Instance olty_inhabited : Inhabited (olty Σ i) := populate (Olty (λ _ _ _, False)%I).

  Global Instance olty_car_ne : NonExpansive oApp.
  Proof. intros n f g Heq. apply Heq. Qed.
  Global Instance lty_car_proper : Proper ((≡) ==> (≡)) oApp.
  Proof. apply ne_proper, olty_car_ne. Qed.

  Program Definition pack φ := Olty (λ args ρ v, □ φ args ρ v)%I.

  Lemma olty_car_pack_id φ `{∀ args ρ v, Persistent (φ args ρ v)} :
    oApp (pack φ) ≡ φ.
  Proof. intros ???. apply: intuitionistic_intuitionistically. Qed.

  Lemma pack_olty_car_id τ : pack (olty_car τ) ≡ τ.
  Proof.
    move: τ => [τ Hp] args ρ v; rewrite /olty_car/=.
    apply: intuitionistic_intuitionistically.
  Qed.
End olty_ofe.

Section olty_subst.
  Context `{Σ : gFunctors} {i : nat}.
  Implicit Types (φ : hoEnvD Σ i) (τ : olty Σ i).

  Global Instance ids_hoEnvD : Ids (hoEnvD Σ i) := λ _, inhabitant.
  Global Instance rename_hoEnvD : Rename (hoEnvD Σ i) :=
    λ r φ args ρ, φ args (r >>> ρ).
  Global Instance hsubst_hoEnvD : HSubst vl (hoEnvD Σ i) :=
    λ sb φ args ρ, φ args (sb >> ρ).

  Ltac renLemmas_hoEnvD :=
    hnf; rewrite /hsubst /hsubst_hoEnvD => /= *;
    do 2 (apply FunctionalExtensionality.functional_extensionality_dep => ?); autosubst.

  Global Instance HSubstLemmas_hoEnvD : HSubstLemmas vl (hoEnvD Σ i).
  Proof. split => //; renLemmas_hoEnvD. Qed.

  (*
    Since substitution lemmas don't use setoids,
    [HSubstLemmas vl (olty Σ)] requires proof irrelevance.
   *)

  Lemma olty_eq τ1 τ2: olty_car τ1 = olty_car τ2 → τ1 = τ2.
  Proof.
    move: τ1 τ2 => [φ1 Hp1] [φ2 Hp2]. rewrite /olty_car /=.
    intros ->. f_equal; exact: ProofIrrelevance.proof_irrelevance.
  Qed.

  Global Instance ids_olty : Ids (olty Σ i) := λ _, inhabitant.
  Global Instance rename_olty : Rename (olty Σ i) :=
    λ r τ, Olty (rename r (olty_car τ)).
  Global Instance hsubst_olty : HSubst vl (olty Σ i) :=
    λ sb τ, Olty (olty_car τ).|[sb].

  Global Instance hsubstLemmas_olty : HSubstLemmas vl (olty Σ i).
  Proof.
    split => [T|//|s1 s2 T]; apply olty_eq; case: T => [φ?];
      rewrite /hsubst /hsubst_olty /olty_car.
    all: by rewrite ?hsubst_id -?hsubst_comp.
  Qed.

  Lemma olty_subst_compose_ind τ args ρ1 ρ2 v: τ.|[ρ1] args ρ2 v ⊣⊢ τ args (ρ1 >> ρ2) v.
  Proof. done. Qed.

  Lemma olty_subst_compose τ args ρ1 ρ2 ρ3 :
    ρ1 >> ρ2 = ρ3 → oApp τ.|[ρ1] args ρ2 ≡ oApp τ args ρ3.
  Proof. by move=> <-. Qed.

  Lemma olty_weaken_one τ args ρ:
     oApp τ.|[ren (+1)] args ρ ≡ oApp τ args (stail ρ).
  Proof. apply olty_subst_compose. autosubst. Qed.

  Lemma olty_subst_one τ v w args ρ:
    oApp τ.|[v/] args ρ w ≡ oApp τ args (v.[ρ] .: ρ) w.
  Proof. apply olty_subst_compose. autosubst. Qed.
End olty_subst.

Notation oClose φ := (olty_car φ vnil : envD _).

Definition sCtx Σ := list (olty Σ 0).

Fixpoint env_oltyped {Σ} (Γ : sCtx Σ) (ρ : var → vl) : iProp Σ :=
  match Γ with
  | φ :: Γ' => env_oltyped Γ' (stail ρ) ∧ oClose φ ρ (shead ρ)
  | nil => True
  end%I.
Notation "⟦ Γ ⟧*" := (env_oltyped Γ).

Section olty_ofe_2.
  Context `{Σ : gFunctors} {i : nat}.
  Implicit Types (φ : hoEnvD Σ i) (τ : olty Σ i).

  Global Instance env_oltyped_persistent (Γ : sCtx Σ) ρ: Persistent (⟦ Γ ⟧* ρ).
  Proof. elim: Γ ρ => [|τ Γ IHΓ] ρ /=; apply _. Qed.

  Lemma interp_env_lookup Γ ρ (τ : olty Σ 0) x:
    Γ !! x = Some τ →
    ⟦ Γ ⟧* ρ -∗ oClose τ.|[ren (+x)] ρ (ρ x).
  Proof.
    elim: Γ ρ x => [//|τ' Γ' IHΓ] ρ x Hx /=.
    iDestruct 1 as "[Hg Hv]". move: x Hx => [ [->] | x Hx] /=.
    - rewrite hsubst_id. by [].
    - rewrite hrenS.
      iApply (olty_weaken_one (τ.|[ren (+x)])).
      iApply (IHΓ (stail ρ) x Hx with "Hg").
  Qed.

  Definition olty0 (φ : envD Σ)`{∀ ρ v, Persistent (φ ρ v)} : olty Σ 0 :=
    Olty (vopen φ).

  (** We can define once and for all basic "logical" types: top, bottom, and, or, later and μ. *)
  Definition oTop : olty Σ i := Olty (λ args ρ v, True)%I.

  Definition oBot : olty Σ i := Olty (λ args ρ v, False)%I.

  Definition oAnd τ1 τ2 : olty Σ i := Olty (λ args ρ v, τ1 args ρ v ∧ τ2 args ρ v)%I.

  Definition oOr τ1 τ2 : olty Σ i := Olty (λ args ρ v, τ1 args ρ v ∨ τ2 args ρ v)%I.

  Definition eLater n (φ : hoEnvD Σ i) : hoEnvD Σ i := (λ args ρ v, ▷^n φ args ρ v)%I.
  Definition oLater τ := Olty (eLater 1 τ).

  Lemma oLater_eq τ args ρ v : oLater τ args ρ v = (▷ τ args ρ v)%I.
  Proof. done. Qed.

  Definition ho_oMu {i} (τ : olty Σ i) : olty Σ i := Olty (λ args ρ v, τ args (v .: ρ) v).

  Definition oMu (τ : olty Σ 0) : olty Σ 0 := ho_oMu τ.

  Lemma ho_oMu_eq (τ : olty Σ i) args ρ v : ho_oMu τ args ρ v = τ args (v .: ρ) v.
  Proof. done. Qed.

  Lemma interp_TMu_ren (T : olty Σ i) args ρ v: ho_oMu T.|[ren (+1)] args ρ v ≡ T args ρ v.
  Proof. rewrite ho_oMu_eq (olty_weaken_one T args _ v) stail_eq. by []. Qed.

  Definition interp_expr `{dlangG Σ} (φ : hoEnvD Σ 0) : envPred tm Σ :=
    λ ρ t, WP t {{ vclose φ ρ }} %I.
  Global Arguments interp_expr /.

  Definition oTSel0 `{dlangG Σ} s σ :=
    olty0 (λ ρ v, ∃ ψ, s ↗[ σ ] ψ ∧ ▷ □ ψ v)%I.
End olty_ofe_2.

Arguments oltyO : clear implicits.
End OLty.

Module Type OLtyJudgements (Import VS: VlSortsFullSig) (Import LVS : LiftWp VS).
Include OLty VS LVS.
Section judgments.
  Context `{dlangG Σ}.
  Implicit Types (τ : olty Σ 0).

  Definition step_indexed_ivstp Γ τ1 τ2 i j: iProp Σ :=
    □∀ ρ v,
      ⟦Γ⟧*ρ → ▷^i oClose τ1 ρ v → ▷^j oClose τ2 ρ v.
  Global Arguments step_indexed_ivstp /.

  Definition ietp Γ τ e : iProp Σ :=
    □∀ ρ, ⟦Γ⟧* ρ → interp_expr τ ρ (e.|[ρ]).
  Global Arguments ietp /.

  Definition step_indexed_ietp Γ τ e i: iProp Σ :=
    □∀ ρ, ⟦Γ⟧* ρ → interp_expr (eLater i τ) ρ (e.|[ρ]).
  Global Arguments step_indexed_ietp /.

End judgments.

Notation "Γ ⊨ e : τ" := (ietp Γ τ e) (at level 74, e, τ at next level).
Notation "Γ ⊨ e : τ , i" := (step_indexed_ietp Γ τ e i) (at level 74, e, τ at next level).
Notation "Γ ⊨ T1 , i <: T2 , j " := (step_indexed_ivstp Γ T1 T2 i j) (at level 74, T1, T2, i, j at next level).

Section typing.
  Context `{dlangG Σ}.
  Implicit Types (τ : olty Σ 0).

  Lemma iterate_TLater_later i τ ρ v:
    oClose (iterate oLater i τ) ρ v ≡ vclose (eLater i τ) ρ v.
  Proof.
    elim: i => [//|i IHi]. by rewrite iterate_S oLater_eq IHi.
  Qed.

  Lemma T_Var Γ x τ
    (Hx : Γ !! x = Some τ):
    (*──────────────────────*)
    Γ ⊨ of_val (ids x) : τ.|[ren (+x)].
  Proof.
    iIntros "/= !>" (ρ) "#Hg"; rewrite hsubst_of_val -wp_value'.
    by rewrite interp_env_lookup // id_subst.
  Qed.

  Lemma andstp1 Γ τ1 τ2 i : Γ ⊨ oAnd τ1 τ2 , i <: τ1 , i.
  Proof. iIntros "!>" (??) "#Hg #[$ _]". Qed.

  Lemma andstp2 Γ τ1 τ2 i : Γ ⊨ oAnd τ1 τ2 , i <: τ2 , i.
  Proof. iIntros "!>" (??) "#Hg #[_ $]". Qed.
End typing.

End OLtyJudgements.
