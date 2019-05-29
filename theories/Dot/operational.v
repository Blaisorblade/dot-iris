From iris.program_logic Require Import ectx_language ectxi_language.
From iris.algebra Require Import ofe agree.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.iprop (* For gname *)
     lib.saved_prop.
From D.pure_program_logic Require Export weakestpre.

From D Require Import tactics.
From D.Dot Require Export syn.

Implicit Types
         (T: ty) (v: vl) (t e: tm) (d: dm) (ds: dms) (vs: vls)
         (Γ : ctx).
(** Substitute object inside itself (to give semantics to the "self"
    variable). To use when descending under the [vobj] binder. *)
Definition selfSubst ds: dms := ds.|[vobj ds/].

(* Unset Program Cases. *)
(* Definition gmap_of_dms ds: gmap label dm := map_of_list ds. *)
(* Definition dms_lookup l ds := gmap_of_dms ds !! l. *)
(* Arguments gmap_of_dms /. *)
(* Arguments dms_lookup /. *)

Definition objLookup v (l: label) d: Prop :=
  ∃ ds, v = vobj ds ∧ (dms_lookup l (selfSubst ds)) = Some d.
Notation "v @ l ↘ d" := (objLookup v l d) (at level 20).

(** Instead of letting obj_opens_to autounfold,
    provide tactics to show it's deterministic and so on. *)

(** Rewrite v ↗ ds to vobj ds' ↗ ds. *)
Ltac simplOpen ds :=
  lazymatch goal with
  | H: ?v @ ?l ↘ ?d |-_=>
    inversion H as (ds & -> & _)
  end.

(** Determinacy of obj_opens_to. *)
Lemma objLookupDet v l d1 d2: v @ l ↘ d1 -> v @ l ↘ d2 -> d1 = d2.
Proof.
  rewrite /objLookup; intros; ev; by subst; injectHyps; optFuncs_det.
Qed.
Ltac objLookupDet :=
  lazymatch goal with
  | H1: ?v @ ?l ↘ ?d1, H2: ?v @ ?l ↘ ?d2 |- _=>
    assert (d2 = d1) as ? by (eapply objLookupDet; eassumption); injectHyps
  end.

(** Instantiating iris with Dot *)
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
| ProjCtx (l: label)
| SkipCtx.

Definition fill_item (Ki : ectx_item) (e : tm) : tm :=
  match Ki with
  | AppLCtx e2 => tapp e e2
  | AppRCtx v1 => tapp (tv v1) e
  | ProjCtx l => tproj e l
  | TSkipCtx => tskip e
  end.

Definition state := unit.
Definition observation := unit.

Inductive head_step : tm -> state -> list observation -> tm -> state -> list tm -> Prop :=
| st_beta t1 v2 σ:
    head_step (tapp (tv (vabs t1)) (tv v2)) σ [] (t1.|[v2/]) σ []
| st_proj ds l σ v:
    dms_lookup l (selfSubst ds) = Some (dvl v) ->
    head_step (tproj (tv (vobj ds)) l) σ [] (tv v) σ []
| st_skip v σ:
    head_step (tskip (tv v)) σ [] (tv v) σ [].

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert v; induction e; intros; simplify_option_eq; auto with f_equal.
Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Local Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
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
  split; eauto using of_to_val, val_stuck, fill_item_val,
    fill_item_no_val_inj, head_ctx_step_val with typeclass_instances.
Qed.

End lang.

Export lang.

Canonical Structure dot_ectxi_lang := EctxiLanguage lang.dot_lang_mixin.
Canonical Structure dot_ectx_lang := EctxLanguageOfEctxi dot_ectxi_lang.
Canonical Structure dot_lang := LanguageOfEctx dot_ectx_lang.

From D Require Export gen_iheap saved_interp.

Class dotG Σ := DotG {
  dotG_savior :> savedInterpG Σ vls vl;
  dotG_interpNames : gen_iheapG stamp gname Σ;
}.

Instance dotG_irisG `{dotG Σ} : irisG dot_lang Σ := {
  state_interp σ κs _ := True%I;
  fork_post _ := True%I;
}.

Class dotPreG Σ := DotPreG {
  dotPreG_savior :> savedInterpG Σ vls vl;
  dotPreG_interpNames : gen_iheapPreG stamp gname Σ;
}.

Definition dotΣ := #[savedInterpΣ vls vl; gen_iheapΣ stamp gname].

Instance subG_dotΣ {Σ} : subG dotΣ Σ → dotPreG Σ.
Proof. solve_inG. Qed.

(* For abstracting synToSem. *)
Class dotInterpG Σ := DotInterpG {
  dot_interp: ty -> vls -> vl -> iProp Σ
}.

Notation "s ↦ γ" := (mapsto (hG := dotG_interpNames) s γ)  (at level 20) : bi_scope.
Notation "s ↝ φ" := (∃ γ, s ↦ γ ∗ γ ⤇ φ)%I  (at level 20) : bi_scope.
Notation envD Σ := (vls -c> vl -c> iProp Σ).

Instance Inhϕ: Inhabited (envD Σ).
Proof. constructor. exact (λ _ _, False)%I. Qed.

Section mapsto.
  Context `{!dotG Σ}.
  Global Instance: Persistent (s ↦ γ).
  Proof. apply _. Qed.
  Global Instance: Timeless (s ↦ γ).
  Proof. apply _. Qed.

  Definition allGs gs := (gen_iheap_ctx (hG := dotG_interpNames) gs).
  Global Arguments allGs /.

  Lemma leadsto_agree s (φ1 φ2: envD Σ) ρ v: s ↝ φ1 -∗ s ↝ φ2 -∗ ▷ (φ1 ρ v ≡ φ2 ρ v).
  Proof.
    iIntros "/= #H1 #H2".
    iDestruct "H1" as (γ1) "[Hs1 Hg1]".
    iDestruct "H2" as (γ2) "[Hs2 Hg2]".
    iDestruct (mapsto_agree with "Hs1 Hs2") as %->.
    by iApply (saved_interp_agree _ φ1 φ2).
  Qed.
End mapsto.
