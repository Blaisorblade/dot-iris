From stdpp Require Import proof_irrel.
From iris.algebra Require Import agree gmap.
From iris.base_logic Require Import saved_prop.

Class PersistentFunct (F : rFunctor) := persistent_func :
    ∀ A `{!Cofe A} B `{!Cofe B} (x : rFunctor_car F A B), CoreId x.

Class FullyPersistent (Σ : gFunctors) := fully_persistent :
    ∀ (i : gid Σ), PersistentFunct (gFunctors_lookup Σ i).

Instance fully_persistent_core_id `{fp : FullyPersistent Σ} (x : iResUR Σ) :
  CoreId x.
Proof.
  apply Some_proper; intros i j.
  rewrite lookup_core.
  destruct (x i !! j) as [y|] eqn:Heq; rewrite Heq; last done.
  rewrite /core /=.
  apply fp.
Qed.

Local Arguments uPred_holds !_ _ _.

Instance FullyPersistent_Persistent `{!FullyPersistent Σ} (P : iProp Σ) :
  Persistent P.
Proof.
  split; intros n x Hx Hpx.
  uPred.unseal.
  rewrite /uPred_persistently_def /=.
  rewrite core_id_core; done.
Qed.

Instance FullyPersistent_nil : FullyPersistent gFunctors.nil.
Proof. intros i; inversion i. Qed.

Instance FullyPersistent_app `{!FullyPersistent Σ, !FullyPersistent Σ'} :
  FullyPersistent (gFunctors.app Σ Σ').
Proof.
  intros i.
  apply fin_plus_inv with (i := i); intros;
    [rewrite /= fin_plus_inv_L|rewrite /= fin_plus_inv_R]; auto.
Qed.

Instance FullyPersistent_GFunctor `{!rFunctorContractive F}
         `{fp : !PersistentFunct F} :
  FullyPersistent #[ GFunctor F].
Proof.
  intros ? ? ? ? ?.
  assert (gFunctors_lookup #[GFunctor F] i = GFunctor F) as ->; last done.
  refine (match i as z in fin u return
                fin_to_nat z < 1  →
                ∀ Heq : u = 1,
                gFunctors_lookup #[ GFunctor F]
                                 match Heq in _ = l return fin l with
                                   eq_refl => z
                                 end = GFunctor F with
            @Fin.F1 k => λ Hlt Heq, _ | Fin.FS _ => _
          end (fin_to_nat_lt i) eq_refl); last by simpl; lia.
  destruct k; last lia.
  rewrite (eq_pi _ _ Heq eq_refl) /=; done.
Qed.

Instance PersistentFunct_agree F : PersistentFunct (agreeRF F).
Proof. intros ? ? ? ? ?; apply _. Qed.

(* testing *)
Local Instance PersistentFunct_savedAnythingΣ `{!oFunctorContractive F} :
  FullyPersistent (savedAnythingΣ F).
Proof. apply _. Qed.
