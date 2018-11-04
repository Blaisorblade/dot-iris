From iris.program_logic Require Export ectx_language ectxi_language.
From iris.algebra Require Export ofe.

Require Export Dot.dotsyn.
Require Import Dot.tactics.

Module lang.

Definition to_val (t: tm) : option vl :=
  match t with
  | tv v => Some v
  | _ => None
  end.

Definition of_val: vl -> tm := tv.

Inductive ectx_item :=
| AppLCtx (e2: tm)
| AppRCtx (v1: vl)
| ProjCtx (l: label).

Definition fill_item (Ki : ectx_item) (e : tm) : tm :=
  match Ki with
  | AppLCtx e2 => tapp e e2
  | AppRCtx v1 => tapp (tv v1) e
  | ProjCtx l => tproj e l
  end.

Definition state := unit.
Definition observation := unit.

Fixpoint dms_to_list (ds: dms) : list dm :=
  match ds with
  | dnil => []
  | dcons d ds => d :: dms_to_list ds
  end.

Definition index_dms (i: label) (ds: dms): option dm :=
  dms_to_list ds !! i.

(** Single-variable substitution, based on the Autosubst1 notation. Priorities copied from s .[ sigma ]. *)
Notation "s .[ v /]" := (s .[ v .: var_vl ])
  (at level 2, v at level 200, left associativity,
   format "s .[ v /]" ) : subst_scope.

(** Substitute object inside itself (to give semantics to the "self"
    variable). To use when descending under the [vobj] binder. *)
Definition selfSubst (ds: dms): dms := ds.[vobj ds/].

Definition obj_opens_to v ds: Prop :=
  ∃ ds', v = vobj ds' ∧ selfSubst ds' = ds.
Notation "v ↗ ds" := (obj_opens_to v ds) (at level 20).

(* Instead of letting obj_opens_to autounfold, provide tactics to show it's deterministic and *)

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

Definition dms_proj_val ds l v: Prop :=
  index_dms l ds = Some (dvl v).

Inductive head_step : tm -> state -> list observation -> tm -> state -> list tm -> Prop :=
| st_beta : forall t1 v2,
    head_step (tapp (tv (vabs t1)) (tv v2)) tt [] (t1.[v2/]) tt []
| st_proj : forall ds l v,
    dms_proj_val (selfSubst ds) l v ->
    head_step (tproj (tv (vobj ds)) l) tt [] (tv v) tt []
.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. done. Qed.
  
Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. 
  revert v; induction e; intros; simplify_option_eq; auto with f_equal.
Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

Lemma val_stuck e1 σ1 k e2 σ2 ef :
  head_step e1 σ1 k e2 σ2 ef → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 k e2 σ2 ef :
  head_step (fill_item Ki e) σ1 k e2 σ2 ef → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
    repeat match goal with
           | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
           end; auto.
Qed.

Lemma dot_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
split; apply _ || eauto using to_of_val, of_to_val, val_stuck,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
Qed.


Canonical Structure dot_ectxi_lang := EctxiLanguage lang.dot_lang_mixin.
Canonical Structure dot_ectx_lang := EctxLanguageOfEctxi dot_ectxi_lang.
Canonical Structure dot_lang := LanguageOfEctx dot_ectx_lang.

End lang.
