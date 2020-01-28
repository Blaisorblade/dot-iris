(** ** Semantic types, judgments, etc.
As usual in Iris, semantic types are persistent Iris predicates on values.
Since D* syntactic types can contain variables ranging on values, semantic types take a value substitution as argument.
Using Autosubst 1, we define substitution on semantic types by precomposition:
[ τ.|[s] = λ ρ, τ (ρ >> s) ].
*)
From D Require Import iris_prelude asubst_base asubst_intf dlang.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import language.
From D.pure_program_logic Require Import lifting adequacy.

From Coq Require ProofIrrelevance FunctionalExtensionality.
Import prelude.

Implicit Types (Σ : gFunctors).

(**
"Logical TYpes": persistent Iris predicates over values.
Adapted from
https://gitlab.mpi-sws.org/iris/examples/blob/d4f4153920ea82617c7222aeeb00b6710d51ee03/theories/logrel_heaplang/ltyping.v#L5. *)

Record iPPred vl Σ := IPPred {
  iPPred_car :> vl → iProp Σ;
  iPPred_persistent v : Persistent (iPPred_car v);
}.
Global Arguments IPPred {_ _} _%I {_}.
Global Arguments iPPred_car {_ _} !_ _ /.
Bind Scope iPPred_scope with iPPred.
Delimit Scope iPPred_scope with T.
Global Existing Instance iPPred_persistent.

Section iPPred_ofe.
  Context {vl : Type} {Σ}.
  Notation vpred := (iPPred vl Σ).
  Implicit Types (ψ : vl -d> iPropO Σ) (τ : vpred).

  (* Forces inserting coercions to -d>. *)
  Notation lApp := (iPPred_car : iPPred _ _ → _ -d> _).

  Definition pred_persistent (A : vl -d> iPropO Σ) := ∀ w, Persistent (A w).

  Instance: LimitPreserving pred_persistent.
  Proof.
    apply limit_preserving_forall=> v.
    apply bi.limit_preserving_Persistent => n f g Heq. exact: Heq.
  Qed.

  Instance iPPred_equiv : Equiv vpred := λ A B, lApp A ≡ B.
  Instance iPPred_dist : Dist vpred := λ n A B, lApp A ≡{n}≡ B.
  Lemma iPPred_ofe_mixin : OfeMixin vpred.
  Proof. by apply (iso_ofe_mixin lApp). Qed.
  Canonical Structure iPPredO := OfeT vpred iPPred_ofe_mixin.

  (* Only needed to define Lty using Iris fixpoints (e.g. for normal recursive types). *)
  Global Instance iPPred_cofe : Cofe iPPredO.
  Proof.
    apply (iso_cofe_subtype' pred_persistent IPPred iPPred_car) => //.
    - by move => [].
    - apply _.
  Qed.

  Global Program Instance iPPred_inhabited : Inhabited vpred := populate (IPPred (λ _, False)%I).

  Global Instance iPPred_car_ne : NonExpansive lApp.
  Proof. intros n f g Heq. apply Heq. Qed.
  Global Instance iPPred_car_proper : Proper ((≡) ==> (≡)) lApp.
  Proof. apply ne_proper, iPPred_car_ne. Qed.

  Program Definition pack ψ := IPPred (λ v, □ ψ v)%I.

  Lemma iPPred_car_pack_id ψ `{∀ v, Persistent (ψ v)} :
    lApp (pack ψ) ≡ ψ.
  Proof. intros ?. apply: intuitionistic_intuitionistically. Qed.

  Lemma pack_iPPred_car_id τ : pack (iPPred_car τ) ≡ τ.
  Proof.
    move: τ => [τ Hp] v /=.
    apply: intuitionistic_intuitionistically.
  Qed.

  (*
    Since substitution lemmas don't use setoids,
    [HSubstLemmas vl (olty Σ i)] requires proof irrelevance.
   *)
  Lemma lty_eq τ1 τ2: iPPred_car τ1 = iPPred_car τ2 → τ1 = τ2.
  Proof.
    move: τ1 τ2 => [φ1 Hp1] [φ2 Hp2]. rewrite /iPPred_car.
    intros ->. f_equal; exact: ProofIrrelevance.proof_irrelevance.
  Qed.
End iPPred_ofe.

Global Arguments iPPredO : clear implicits.

Module Type Lty (Import VS: VlSortsFullSig) (Import LVS : LiftWp VS).

Notation lty Σ := (iPPred vl Σ).
Notation ltyO Σ := (iPPredO vl Σ).
Notation Lty := (IPPred (vl := vl)).
Notation lty_car := (iPPred_car (vl := vl)) (only parsing).
(* Forces inserting coercions to -d>. *)
Notation lApp := (iPPred_car : lty _ → _ -d> _).

Global Arguments vopen /.
Global Arguments vclose /.

(* "Open Logical TYpes": persistent Iris predicates over environments and values. *)
Definition olty Σ i := vec vl i -> env -> lty Σ.
Notation oltyO Σ n := (vec vl n -d> env -d> ltyO Σ).

Notation olty_car τ := (λ args ρ v, lty_car (τ args ρ) v).
Definition oApp {Σ i} : olty Σ i -> hoEnvD Σ i := λ φ, olty_car φ.

(* Rename hoEnvD to hoEnv(D?)O. *)
(* Definition hoEnv Σ i := vec vl i → (var → vl) → vl → iProp Σ. *)
(* Definition oiPPred_car {Σ i} : olty Σ i → vec vl i → (var → vl) → vl → iProp Σ := *)
(* Definition oiPPred_car {Σ i} : olty Σ i → hoEnv Σ i :=
  λ τ args ρ v, lty_car (τ args ρ) v. *)

(* Different from normal TyInterp. Better? *)
Class OTyInterp (ty : nat → Type) Σ :=
  oty_interp : ∀ {i}, ty i → olty Σ i.

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

  Lemma hoEnvD_subst_compose_ind φ args ρ1 ρ2 v: φ.|[ρ1] args ρ2 v ⊣⊢ φ args (ρ1 >> ρ2) v.
  Proof. done. Qed.

  Lemma hoEnvD_subst_compose φ args ρ1 ρ2 ρ3 :
    ρ1 >> ρ2 = ρ3 → φ.|[ρ1] args ρ2 ≡ φ args ρ3.
  Proof. by move=> <-. Qed.

  Lemma hoEnvD_weaken_one φ args ρ:
     shift φ args ρ ≡ φ args (stail ρ).
  Proof. apply hoEnvD_subst_compose. autosubst. Qed.

  Lemma hoEnvD_subst_one φ v w args ρ:
    φ.|[v/] args ρ w ≡ φ args (v.[ρ] .: ρ) w.
  Proof. apply hoEnvD_subst_compose. autosubst. Qed.

  Definition Olty (olty_car : vec vl i → (var → vl) → vl → iProp Σ)
   `{∀ args ρ v, Persistent (olty_car args ρ v)}: olty Σ i :=
    λ args ρ, Lty (olty_car args ρ).

  Global Instance ids_olty : Ids (olty Σ i) := λ _, inhabitant.
  Global Program Instance rename_olty : Rename (olty Σ i) :=
    λ r τ, Olty (rename r (olty_car τ)).
  Global Program Instance hsubst_olty : HSubst vl (olty Σ i) :=
    λ sb τ, Olty ((olty_car τ).|[sb]).

  Lemma olty_eq τ1 τ2:
    (∀ args ρ, olty_car τ1 args ρ = olty_car τ2 args ρ) →
    τ1 = τ2.
  Proof. intros * Heq; f_ext => args; f_ext => ρ. apply lty_eq, Heq. Qed.

  Lemma olty_eq' τ1 τ2: olty_car τ1 = olty_car τ2 → τ1 = τ2.
  Proof.
    intros Heq; apply olty_eq => args ρ.
    apply (f_equal_dep _ _ ρ
              (f_equal_dep _ _ args Heq)).
  Qed.

  Global Instance hsubstLemmas_olty : HSubstLemmas vl (olty Σ i).
  Proof.
    split => [T|//|s1 s2 T]; apply olty_eq => args ρ; f_ext => v.
    all: by rewrite /hsubst/= ?hsubst_id -?hsubst_comp.
  Qed.

  Lemma olty_subst_compose_ind τ args ρ1 ρ2 v: τ.|[ρ1] args ρ2 v ⊣⊢ τ args (ρ1 >> ρ2) v.
  Proof. apply hoEnvD_subst_compose_ind. Qed.

  Lemma olty_subst_compose τ args ρ1 ρ2 ρ3 :
    ρ1 >> ρ2 = ρ3 → τ.|[ρ1] args ρ2 ≡ τ args ρ3.
  Proof. apply hoEnvD_subst_compose. Qed.

  Lemma olty_weaken_one τ args ρ:
     shift τ args ρ ≡ τ args (stail ρ).
  Proof. apply hoEnvD_weaken_one. Qed.

  Lemma olty_subst_one τ v w args ρ:
    τ.|[v/] args ρ w ≡ τ args (v.[ρ] .: ρ) w.
  Proof. apply hoEnvD_subst_one. Qed.
End olty_subst.

Notation oClose τ := (τ vnil).

Definition sCtx Σ := listO (oltyO Σ 0).

Fixpoint env_oltyped {Σ} (Γ : sCtx Σ) (ρ : var → vl) : iProp Σ :=
  match Γ with
  | φ :: Γ' => env_oltyped Γ' (stail ρ) ∧ oClose φ ρ (shead ρ)
  | nil => True
  end%I.
Notation "s⟦ Γ ⟧*" := (env_oltyped Γ).

Section olty_ofe_2.
  Context `{Σ : gFunctors} {i : nat}.
  Implicit Types (φ : hoEnvD Σ i) (τ : olty Σ i).

  Global Instance env_oltyped_persistent (Γ : sCtx Σ) ρ: Persistent (s⟦ Γ ⟧* ρ).
  Proof. elim: Γ ρ => [|τ Γ IHΓ] ρ /=; apply _. Qed.

  Lemma interp_env_lookup Γ ρ (τ : olty Σ 0) x:
    Γ !! x = Some τ →
    s⟦ Γ ⟧* ρ -∗ oClose (shiftN x τ) ρ (ρ x).
  Proof.
    elim: Γ ρ x => [//|τ' Γ' IHΓ] ρ x Hx /=.
    iDestruct 1 as "[Hg Hv]". move: x Hx => [ [->] | x Hx] /=.
    - rewrite hsubst_id. by [].
    - rewrite hrenS.
      iApply (olty_weaken_one (shiftN x τ)).
      iApply (IHΓ (stail ρ) x Hx with "Hg").
  Qed.

  Definition olty0 (φ : envD Σ) `{∀ ρ v, Persistent (φ ρ v)} : olty Σ 0 :=
    Olty (vopen φ).

  (** We can define once and for all basic "logical" types: top, bottom, and, or, later and μ. *)
  Definition oTop : olty Σ i := Olty (λ args ρ v, True)%I.

  Definition oBot : olty Σ i := Olty (λ args ρ v, False)%I.

  Definition oAnd τ1 τ2 : olty Σ i := Olty (λ args ρ v, τ1 args ρ v ∧ τ2 args ρ v)%I.

  Definition oOr τ1 τ2 : olty Σ i := Olty (λ args ρ v, τ1 args ρ v ∨ τ2 args ρ v)%I.

  Definition eLater n (φ : hoEnvD Σ i) : hoEnvD Σ i := (λ args ρ v, ▷^n φ args ρ v)%I.
  Global Arguments eLater /.
  Definition oLater τ := Olty (eLater 1 τ).

  Lemma oLater_eq τ args ρ v : oLater τ args ρ v = (▷ τ args ρ v)%I.
  Proof. done. Qed.

  Definition ho_oMu {i} (τ : olty Σ i) : olty Σ i := Olty (λ args ρ v, τ args (v .: ρ) v).

  Definition oMu (τ : olty Σ 0) : olty Σ 0 := ho_oMu τ.

  Lemma ho_oMu_eq (τ : olty Σ i) args ρ v : ho_oMu τ args ρ v = τ args (v .: ρ) v.
  Proof. done. Qed.

  Lemma interp_TMu_ren (T : olty Σ i) args ρ v: ho_oMu (shift T) args ρ v ≡ T args ρ v.
  Proof. rewrite /= (hoEnvD_weaken_one T args _ v) stail_eq. by []. Qed.

  Definition interp_expr `{dlangG Σ} (φ : hoEnvD Σ 0) : envPred tm Σ :=
    λ ρ t, WP t {{ vclose φ ρ }} %I.
  Global Arguments interp_expr /.

  Definition oTSel0 `{dlangG Σ} s σ :=
    olty0 (λ ρ v, ∃ ψ, s ↗[ σ ] ψ ∧ ▷ □ ψ v)%I.
End olty_ofe_2.
End Lty.

Module Type LtyJudgements (Import VS: VlSortsFullSig) (Import LVS : LiftWp VS).
Include Lty VS LVS.
Section judgments.
  Context `{dlangG Σ}.
  Implicit Types (τ : oltyO Σ 0).

  Definition sstpi Γ τ1 τ2 i j: iProp Σ :=
    □∀ ρ v,
      s⟦Γ⟧*ρ → ▷^i oClose τ1 ρ v → ▷^j oClose τ2 ρ v.
  Global Arguments sstpi /.

  Definition setp Γ τ e : iProp Σ :=
    □∀ ρ, s⟦Γ⟧* ρ → interp_expr τ ρ (e.|[ρ]).
  Global Arguments setp /.

  Definition setpi Γ τ e i: iProp Σ :=
    □∀ ρ, s⟦Γ⟧* ρ → interp_expr (eLater i τ) ρ (e.|[ρ]).
  Global Arguments setpi /.

End judgments.

Notation "Γ s⊨ e : τ" := (setp Γ τ e) (at level 74, e, τ at next level).
Notation "Γ s⊨ e : τ , i" := (setpi Γ τ e i) (at level 74, e, τ at next level).
Notation "Γ s⊨ T1 , i <: T2 , j " := (sstpi Γ T1 T2 i j) (at level 74, T1, T2, i, j at next level).

Section typing.
  Context `{dlangG Σ}.
  Implicit Types (τ : olty Σ 0).

  Lemma iterate_TLater_later i τ ρ v:
    oClose (iterate oLater i τ) ρ v ≡ vclose (eLater i τ) ρ v.
  Proof. elim: i => [//|i IHi]. by rewrite iterate_S /= IHi. Qed.

  Lemma T_Var Γ x τ
    (Hx : Γ !! x = Some τ):
    (*──────────────────────*)
    Γ s⊨ of_val (ids x) : shiftN x τ.
  Proof.
    iIntros "/= !>" (ρ) "#Hg"; rewrite hsubst_of_val -wp_value'.
    by rewrite interp_env_lookup // id_subst.
  Qed.

  Lemma andstp1 Γ τ1 τ2 i : Γ s⊨ oAnd τ1 τ2 , i <: τ1 , i.
  Proof. iIntros "!>" (??) "#Hg #[$ _]". Qed.

  Lemma andstp2 Γ τ1 τ2 i : Γ s⊨ oAnd τ1 τ2 , i <: τ2 , i.
  Proof. iIntros "!>" (??) "#Hg #[_ $]". Qed.
End typing.

End LtyJudgements.
