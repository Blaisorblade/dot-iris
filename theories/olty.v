From D Require Import prelude tactics asubst_lemmas asubst_base.

From D Require Import swap_later_impl proofmode_extra.
(* From D.pure_program_logic Require Import lifting. *)
From iris.program_logic Require Import language.
From iris.base_logic Require Import lib.iprop.
(* From iris.proofmode Require Import tactics. *)

Import uPred.

Module OLty (values: Values).

Import values.
Module M := SortsLemmas values.
Export M.

Implicit Types (v: vl) (ρ vs : vls).
Implicit Types (Σ : gFunctors).

(** "Open Logical TYpe". *)
Notation envD Σ := (vls -c> vl -c> iProp Σ).

Record olty Σ := Olty {
  olty_car : envD Σ;
  olty_persistent ρ v : Persistent (olty_car ρ v)
}.
Arguments Olty {_} _%I {_}.
(* Arguments olty_car {_} _ _ _: simpl never. *)
Arguments olty_car {_} _ _ _ /. (* TODO *)
Bind Scope olty_scope with olty.
Delimit Scope olty_scope with T.
Existing Instance olty_persistent.

Fail Definition testCoerce `(φ: olty Σ) ρ := φ ρ.
Definition olty2fun `(o: olty Σ) ρ := olty_car o ρ.
Coercion olty2fun: olty >-> Funclass.
Definition testCoerce `(φ: olty Σ) ρ := φ ρ.


Section olty_ofe.
  Context `{Σ : gFunctors}.
  Instance olty_equiv : Equiv (olty Σ) := λ A B, olty_car A ≡ B.
  Instance olty_dist : Dist (olty Σ) := λ n A B, olty_car A ≡{n}≡ B.
  Lemma olty_ofe_mixin : OfeMixin (olty Σ).
  Proof. by apply (iso_ofe_mixin olty_car). Qed.
  Canonical Structure oltyC := OfeT (olty Σ) olty_ofe_mixin.

  Global Instance olty_cofe : Cofe oltyC.
  Proof.
    apply (iso_cofe_subtype' (λ A : envD Σ, ∀ ρ w, Persistent (A ρ w))
      (@Olty _) olty_car)=> //.
    - apply _.
    - apply limit_preserving_forall=> ρ; apply limit_preserving_forall=> w.
      apply bi.limit_preserving_Persistent => n ?? H. exact: H.
  Qed.

  Global Instance olty_inhabited : Inhabited (olty Σ) := populate (Olty inhabitant).
  Global Instance olty_car_ne: NonExpansive (@olty_car Σ).
  Proof. by intros ??. Qed.
  Global Instance lty_car_proper : Proper ((≡) ==> (≡)) (@olty_car Σ) := _.
  Proof. apply ne_proper, olty_car_ne. Qed.
End olty_ofe.
Arguments oltyC : clear implicits.

Definition pack {Σ} (φ: envD Σ): olty Σ := Olty (λ ρ v, □ φ ρ v)%I.
Lemma persistently_id `(P : iProp Σ) `{!Persistent P}: □P ⊣⊢ P.
(* Proof. by iSplit; iIntros. Qed. *)
Proof. apply: intuitionistic_intuitionistically. Qed.

Lemma olty_car_pack_id `(φ : envD Σ) `{∀ ρ v, Persistent (φ ρ v)}: olty_car (pack φ) ≡ φ.
Proof. move => ??/=. apply: intuitionistic_intuitionistically. Qed.

(* Arguments olty2fun: simpl never. *)
Lemma pack_olty_car_id `(φ: olty Σ): pack (olty_car φ) ≡ φ.
Proof. move:φ=>[]????/=. apply: intuitionistic_intuitionistically. Qed.

Class TyInterp ty Σ := DotInterpG {
  ty_interp: ty → olty Σ
}.
Class Closeable s := nclosed_s : s → nat → Prop.
Instance closeable_sort s `{Sort s} : Closeable s := nclosed.
Instance closeable_vl : Closeable vl := nclosed_vl.

Section judgments.
Context `{TyInterp ty Σ}.
Notation sCtx := (list (olty Σ)).
Notation ctx := (list ty).

Notation "⟦ T ⟧" := (ty_interp T).

Fixpoint env_oltyped (Γ : sCtx) ρ : iProp Σ :=
  match Γ, ρ with
  | φ :: Γ', v :: ρ => env_oltyped Γ' ρ ∗ φ (v::ρ) v
  | nil, nil => True
  | _, _ => False
  end%I.
Instance env_oltyped_persistent (Γ : sCtx) ρ: Persistent (env_oltyped Γ ρ).
Proof. elim: Γ ρ => [|τ Γ IHΓ] [|v ρ] /=; apply _. Qed.

Definition ty_interp_env (Γ : ctx) : sCtx := map ty_interp Γ.
Definition env_typed (Γ : ctx) : vls -c> iProp Σ := env_oltyped (ty_interp_env Γ).

Instance env_typed_persistent `{TyInterp ty Σ} Γ ρ : Persistent (env_typed Γ ρ) := env_oltyped_persistent _ _.

Definition judgment Σ s : Type := s * (vls -c> s -c> iProp Σ).

Definition judgment_holds `{Closeable s} (Γ : sCtx) (J : judgment Σ s) :=
  (⌜ nclosed_s (fst J) (length Γ) ⌝ ∗ □∀ ρ, env_oltyped Γ ρ → (snd J) ρ (fst J))%I.
Notation "Γ ⊨ J" := (judgment_holds Γ J) (at level 74, J at next level).
Global Arguments judgment_holds /.

Definition ivtp (φ: olty Σ) v : judgment Σ vl := (v, olty_car φ).
Global Arguments ivtp /.

(* DOT/D<: judgments are indexed by [⋅]. *)
Notation "v v⋅: φ" := (ivtp φ v) (at level 73).
Definition judge_me Γ v φ := Γ ⊨ v v⋅: φ.
(* About judge_me. *)
  (* Context {Λ: language}.
  Fail Definition interp_expr (φ : olty Σ) :=
    λ ρ t, WP t {{ φ ρ }} %I. *)
  (* Global Arguments interp_expr /. *)

End judgments.
(* Module Type Foo.
Parameter vlL : language. with vlL.vl := vl. *)


End OLty.
