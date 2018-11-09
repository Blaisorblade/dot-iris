(*
Lemmas on SynFuncs.v needed for proofs on the operational semantics.
To reduce compile times, unary_lr should not depend on this file.
This file should load as little Iris code as possible, to reduce compile times. But we must import operational.
 *)
Require Import Dot.tactics.
Require Export Dot.dotsyn.
Require Export Dot.operational.
(* Require Export Dot.synFuncs. *)

(* Require Import ssreflect. *)
(* From stdpp Require Import tactics. *)

(* Module SynLemmas (gnameMod: type). *)
(* Import gnameMod. *)
(* Module SynFuncsG := SynFuncs gnameMod. *)
(* Import SynFuncsG. *)

Bind Scope dms_scope with dms.
Open Scope dms_scope.
Notation " [@ ] " := dnil (format "[@ ]") : dms_scope.
Notation " [@ x ] " := (dcons x dnil) : dms_scope.
Notation " [@ x ; y ; .. ; z ] " := (dcons x (dcons y .. (dcons z dnil) ..))
                                    : dms_scope.

Lemma indexr_max {X} (T: X) i vs:
                       indexr i vs = Some T ->
                       i < length vs.
Proof.
  induction vs; first done; rewrite /lt in IHvs |- *; move => /= H.
  case_decide; subst; [ lia | eauto ].
Qed.
Hint Resolve indexr_max.

Lemma indexr_extend {X} vs n x (T: X):
                       indexr n vs = Some T ->
                       indexr n (x::vs) = Some T.
Proof.
  move => H /=; assert (n < length vs) by naive_solver; by case_decide; first lia.
Qed.

Lemma index_dms_extend l d ds dr:
  index_dms l ds = Some dr ->
  index_dms l (dcons d ds) = Some dr.
Proof. rewrite /index_dms; cbn -[indexr]. by apply indexr_extend. Qed.

Lemma index_dcons d ds: index_dms (dms_length ds) (dcons d ds) = Some d.
Proof. rewrite /index_dms /dms_length /=; by case_decide. Qed.
Hint Resolve index_dcons.

(** Rewrite v ↗ ds to vobj ds' ↗ ds. *)
Ltac simplOpen ds' :=
  lazymatch goal with
  | H: ?v ↗ ?ds |-_=>
    inversion H as (ds' & -> & _)
  end.

(** Determinacy of obj_opens_to. *)
Lemma openDet v ds1 ds2: v ↗ ds1 -> v ↗ ds2 -> ds1 = ds2.
Proof.
  rewrite /obj_opens_to; intros; ev; by optFuncs_det.
Qed.
Ltac openDet :=
  lazymatch goal with
  | H1: ?v ↗ ?ds1, H2: ?v ↗ ?ds2 |- _=>
    assert (ds1 = ds2) as <- by (eapply openDet; eassumption)
  end.

Arguments dms_proj_val /.

(* End SynLemmas. *)