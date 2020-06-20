(** * Show all of Iris propositions are persistent when resources are idempotent (like in our case). *)
From iris.algebra Require Import agree gmap.
From iris.base_logic Require Import lib.iprop.

From D Require Import cmra_prop_lift.

Set Suggest Proof Using.
Set Default Proof Using "Type".

Class CmraPersistent (M : cmraT) :=
  cmra_persistent (x : M) :> CoreId x.

Section CmraPersistentLaws.
  Local Arguments uPred_holds {_} !_ _ _.

  Global Instance CmraPersistent_Persistent {M : ucmraT} `(!CmraPersistent M)
    (P : uPred M) : Persistent P.
  Proof.
    split => n x Hx Hpx; uPred.unseal.
    rewrite core_id_core. done.
  Qed.
End CmraPersistentLaws.

(** *** Lift [cmra_prop_lift] infrastructure to [CmraPersistent]. *)
Notation PersistentRFunct F := (LiftCPropToRFunctor CmraPersistent F).
Notation PersistentGFunct Σ := (LiftCPropToGFunctors CmraPersistent Σ).

Instance PersistentGFunct_nil : LiftCPropToGFunctors_nil_type CmraPersistent.
Proof. apply LiftCPropToGFunctors_nil. Qed.

Instance PersistentGFunct_app : LiftCPropToGFunctors_app_type CmraPersistent.
Proof. apply LiftCPropToGFunctors_app. Qed.

Instance PersistentGFunct_GFunctor `{!rFunctorContractive F} :
  LiftCPropToGFunctors_GFunctor_type F CmraPersistent.
Proof. apply LiftCPropToGFunctors_GFunctor. Qed.

(** *** Show that [iResUR] and [iProp] lift [CmraPersistent], using [cmra_prop_lift]. *)
Instance CmraPersistent_discrete_funUR {A} (B : A → ucmraT)
  `(∀ i, CmraPersistent (B i)) :
  CmraPersistent (discrete_funUR B).
Proof.
  move=> f; unfold CoreId.
  apply Some_proper => a.
  apply: core_id_core.
Qed.

Instance CmraPersistent_gmapUR `{Countable A} `(!CmraPersistent T):
  CmraPersistent (gmapUR A T).
Proof.
  intros j.
  apply Some_proper => k.
  rewrite lookup_core.
  case: (j !! k) => [y|//].
  apply: core_id.
Qed.

Instance CmraPersistent_iResUR `(fp : PersistentGFunct Σ) :
  CmraPersistent (iResUR Σ) | 100 := lift_cprop_iResUR.

(** * Show that our actual resources satisfy [CmraPersistent]. *)
Instance CmraPersistent_agreeR F : CmraPersistent (agreeR F).
Proof. intros ?; apply _. Qed.

(* Currently unused instances. *)
Instance CmraPersistent_optionUR `{!CmraPersistent A}: CmraPersistent (optionUR A).
Proof.
  intros x.
  apply Some_proper.
  apply: core_id_core.
Qed.
