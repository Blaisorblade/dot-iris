From D Require Import iris_prelude asubst_base asubst_intf dlang.
(* From D.pure_program_logic Require Import lifting. *)
From iris.program_logic Require Import language.
From D.pure_program_logic Require Import lifting adequacy.
From D Require Export gen_iheap saved_interp.

Module Type OLty (Import sorts: SortsIntf).

(* Instead of duplicating [envD], Include LiftWp: *)
(* Notation envD Σ := (vls -d> vl -d> iProp Σ). *)
Include LiftWp sorts.

Section olty_limit_preserving.
  Context `{Σ : gFunctors}.

  Definition envD_persistent (A : envD Σ) := ∀ ρ w, Persistent (A ρ w).

  Global Instance: LimitPreserving envD_persistent.
  Proof.
    apply limit_preserving_forall=> ρ; apply limit_preserving_forall=> w.
      apply bi.limit_preserving_Persistent => n ?? H. exact: H.
  Qed.
End olty_limit_preserving.

(**
"Open Logical TYpes": persistent Iris predicates over environments
and values. Adapted from
https://gitlab.mpi-sws.org/iris/examples/blob/d4f4153920ea82617c7222aeeb00b6710d51ee03/theories/logrel_heaplang/ltyping.v#L5. *)
Record olty Σ := Olty {
  olty_car : envD Σ;
  olty_persistent ρ v : Persistent (olty_car ρ v)
}.
Arguments Olty {_} _%I {_}.
Arguments olty_car {_} _ _ _ /.
Bind Scope olty_scope with olty.
Delimit Scope olty_scope with T.
Existing Instance olty_persistent.

Fail Definition testCoerce `(φ: olty Σ) ρ := φ ρ.
Definition olty2fun `(o: olty Σ) ρ := olty_car o ρ.
Coercion olty2fun: olty >-> Funclass.
Definition testCoerce `(φ: olty Σ) ρ := φ ρ.

Section olty_ofe.
  Context `{Σ : gFunctors}.
  Implicit Types (φ : envD Σ) (τ : olty Σ).

  Instance olty_equiv : Equiv (olty Σ) := λ A B, olty_car A ≡ B.
  Instance olty_dist : Dist (olty Σ) := λ n A B, olty_car A ≡{n}≡ B.
  Lemma olty_ofe_mixin : OfeMixin (olty Σ).
  Proof. by apply (iso_ofe_mixin olty_car). Qed.
  Canonical Structure oltyC := OfeT (olty Σ) olty_ofe_mixin.

  (* Only needed to define Olty using Iris fixpoints (e.g. for normal recursive types). *)
  Global Instance olty_cofe : Cofe oltyC.
  Proof.
    apply (iso_cofe_subtype' envD_persistent
      (@Olty _) olty_car)=> //; rewrite /envD_persistent; apply _.
  Qed.

  Global Program Instance olty_inhabited : Inhabited (olty Σ) := populate (Olty (λ _ _, False)%I).

  Global Instance olty_car_ne: NonExpansive (@olty_car Σ).
  Proof. by intros ??. Qed.
  Global Instance lty_car_proper : Proper ((≡) ==> (≡)) (@olty_car Σ).
  Proof. apply ne_proper, olty_car_ne. Qed.

  Definition pack φ : olty Σ := Olty (λ ρ v, □ φ ρ v)%I.
  Lemma persistently_id (P : iProp Σ) `{!Persistent P}: □P ⊣⊢ P.
  (* Proof. by iSplit; iIntros. Qed. *)
  Proof. apply: intuitionistic_intuitionistically. Qed.

  Lemma olty_car_pack_id φ `{∀ ρ v, Persistent (φ ρ v)} :
    olty_car (pack φ) ≡ φ.
  Proof.
    move => ?? /=.
    apply: intuitionistic_intuitionistically.
  Qed.

  Lemma pack_olty_car_id τ : pack (olty_car τ) ≡ τ.
  Proof.
    move: τ => []????/=.
    apply: intuitionistic_intuitionistically.
  Qed.
End olty_ofe.
Arguments oltyC : clear implicits.

(* Different from normal TyInterp. Better? *)
Class OTyInterp ty Σ :=
  oty_interp: ty → olty Σ.
End OLty.
