From D Require Import iris_prelude.
From iris.proofmode Require Import tactics.

Section piProp_limit_preserving.
  Context `{Σ : gFunctors}.

  Definition hoEnvD_persistent (A : iPropO Σ) := Persistent A.

  Instance: LimitPreserving hoEnvD_persistent.
  Proof. apply bi.limit_preserving_Persistent => n f g Heq. exact: Heq. Qed.

  Definition restrict A := hoEnvD_persistent A.
  Global Instance: LimitPreserving restrict := _.
End piProp_limit_preserving.

(**
"Logical TYpes": persistent Iris propositions. Adapted from
https://gitlab.mpi-sws.org/iris/examples/blob/d4f4153920ea82617c7222aeeb00b6710d51ee03/theories/logrel_heaplang/ltyping.v#L5. *)
Record piProp Σ := PiProp {
  piProp_car :> iProp Σ;
  piProp_persistent : Persistent piProp_car;
}.
Global Arguments PiProp {_} _%I {_}.
Global Arguments piProp_car {_} _: simpl never.
Bind Scope piProp_scope with piProp.
Delimit Scope piProp_scope with T.
Global Existing Instance piProp_persistent.

Section piProp_ofe.
  Context `{Σ : gFunctors}.
  Implicit Types (ψ : iPropO Σ) (τ : piProp Σ).

  Instance piProp_equiv : Equiv (piProp Σ) := λ A B, piProp_car A ≡ B.
  Instance piProp_dist : Dist (piProp Σ) := λ n A B, piProp_car A ≡{n}≡ B.
  Lemma piProp_ofe_mixin : OfeMixin (piProp Σ).
  Proof. by apply (iso_ofe_mixin piProp_car). Qed.
  Canonical Structure piPropO := OfeT (piProp Σ) piProp_ofe_mixin.

  (* Only needed to define PiProp using Iris fixpoints (e.g. for normal recursive types). *)
  Global Instance piProp_cofe : Cofe piPropO.
  Proof. apply (iso_cofe_subtype' restrict PiProp piProp_car), _ => //. by case. Qed.

  Global Instance piProp_inhabited : Inhabited (piProp Σ) := populate (PiProp False).

  Global Instance piProp_car_ne : NonExpansive piProp_car.
  Proof. intros n f g Heq. apply Heq. Qed.
  Global Instance piProp_car_proper : Proper ((≡) ==> (≡)) piProp_car.
  Proof. apply ne_proper, piProp_car_ne. Qed.

  Definition pack ψ := PiProp (□ ψ).

  Lemma piProp_car_pack_id ψ `{!Persistent ψ} :
    piProp_car (pack ψ) ≡ ψ.
  Proof. apply: intuitionistic_intuitionistically. Qed.

  Lemma pack_piProp_car_id τ : pack (piProp_car τ) ≡ τ.
  Proof.
    move: τ => [τ Hp]; rewrite /piProp_car/=.
    apply: intuitionistic_intuitionistically.
  Qed.
(*
  Lemma piProp_eq τ1 τ2: piProp_car τ1 = piProp_car τ2 → τ1 = τ2.
  Proof.
    move: τ1 τ2 => [φ1 Hp1] [φ2 Hp2]. rewrite /piProp_car /=.
    intros ->. f_equal; exact: ProofIrrelevance.proof_irrelevance.
  Qed. *)
End piProp_ofe.

Arguments piPropO : clear implicits.
