From stdpp Require Import strings.
From D Require Export prelude.
From D Require Import asubst_intf asubst_base.
From iris.program_logic Require ectx_language ectxi_language.

(** This module is included right away. Its only point is asserting explicitly
    what interface it implements. *)
Module VlSorts <: VlSortsFullSig.

Definition label := string.

Inductive vl_ : Type :=
  | var_vl : var -> vl_
  | vnat : nat -> vl_
  | vabs : tm -> vl_
  | vobj : list (label * dm) -> vl_
 with tm : Type :=
  | tv : vl_ -> tm
  | tapp : tm -> tm -> tm
  | tproj : tm -> label -> tm
  | tskip : tm -> tm
 with dm : Type :=
  | dtysem : list vl_ -> stamp -> dm
  | dvl : vl_ -> dm.

Definition vl := vl_.

Definition vls := list vl.
Definition dms := list (label * dm).

Bind Scope dms_scope with dms.
Delimit Scope dms_scope with dms.

Implicit Types (v : vl) (t : tm) (d : dm) (ds : dms) (vs : vls) (l : label).

Fixpoint dms_lookup l ds : option dm :=
  match ds with
  | [] => None
  | (l', d) :: ds =>
    match (decide (l = l')) with
    | left Heq => Some d
    | right _ => dms_lookup l ds
    end
  end.

Definition dms_has ds l d := dms_lookup l ds = Some d.
Definition dms_hasnt ds l := dms_lookup l ds = None.

Instance inh_vl : Inhabited vl := populate (vnat 0).
Instance inh_tm : Inhabited tm := populate (tv inhabitant).
Instance inh_dm : Inhabited dm := populate (dvl inhabitant).

Instance ids_vl : Ids vl := var_vl.

Instance inj_ids : Inj (=) (=@{vl}) ids.
Proof. by move=>??[]. Qed.

Instance ids_tm : Ids tm := inh_ids.
Instance ids_dm : Ids dm := inh_ids.
Instance ids_vls : Ids vls := _.
Instance ids_dms : Ids dms := _.

Fixpoint vl_rename (sb : var → var) v : vl :=
  let a := tm_rename : Rename tm in
  let b := vl_rename : Rename vl in
  let c := dm_rename : Rename dm in
  match v with
  | var_vl x => var_vl (sb x)
  | vnat n => vnat n
  | vabs t => vabs (rename (upren sb) t)
  | vobj d => vobj (rename (upren sb) d)
  end with
tm_rename (sb : var → var) t : tm :=
  let a := tm_rename : Rename tm in
  let b := vl_rename : Rename vl in
  match t with
  | tv v => tv (rename sb v)
  | tapp t1 t2 => tapp (rename sb t1) (rename sb t2)
  | tproj t l => (tproj (rename sb t) l)
  | tskip t => tskip (rename sb t)
  end with
dm_rename (sb : var → var) d : dm :=
  let a := vl_rename : Rename vl in
  match d with
  | dtysem lv γ => dtysem (rename sb lv) γ
  | dvl v => dvl (rename sb v)
  end.

Instance rename_vl : Rename vl := vl_rename.
Instance rename_tm : Rename tm := tm_rename.
Instance rename_dm : Rename dm := dm_rename.

Hint Rewrite @list_rename_fold @list_pair_rename_fold : autosubst.

Fixpoint vl_subst (sb : var → vl) v : vl :=
  let a := tm_hsubst : HSubst vl tm in
  let b := dm_hsubst : HSubst vl dm in
  match v with
  | var_vl x => sb x
  | vnat n => vnat n
  | vabs t => vabs (hsubst (up sb) t)
  | vobj d => vobj (hsubst (up sb) d)
  end with
tm_hsubst (sb : var → vl) t : tm :=
  let a := tm_hsubst : HSubst vl tm in
  let b := vl_subst : Subst vl in
  match t with
  | tv v => tv (subst sb v)
  | tapp t1 t2 => tapp (hsubst sb t1) (hsubst sb t2)
  | tproj t l => (tproj (hsubst sb t) l)
  | tskip t => tskip (hsubst sb t)
  end with
dm_hsubst (sb : var → vl) d : dm :=
  let a := vl_subst : Subst vl in
  match d with
  | dtysem lv γ => dtysem (hsubst sb lv) γ
  | dvl v => dvl (subst sb v)
  end.

Instance subst_vl : Subst vl := vl_subst.
Instance hsubst_tm : HSubst vl tm := tm_hsubst.
Instance hsubst_dm : HSubst vl dm := dm_hsubst.

Lemma vl_eq_dec v1 v2 : Decision (v1 = v2)
with
tm_eq_dec t1 t2 : Decision (t1 = t2)
with
dm_eq_dec d1 d2 : Decision (d1 = d2).
Proof.
   all: rewrite /Decision; decide equality;
       repeat first [apply vl_eq_dec | apply tm_eq_dec |
            apply @prod_eq_dec | apply @list_eq_dec | apply nat_eq_dec |
            apply positive_eq_dec | apply string_eq_dec]; trivial.
Qed.

Instance vl_eq_dec' : EqDecision vl := vl_eq_dec.
Instance tm_eq_dec' : EqDecision tm := tm_eq_dec.
Instance dm_eq_dec' : EqDecision dm := dm_eq_dec.
Instance vls_eq_dec' : EqDecision vls := list_eq_dec.
Instance dms_eq_dec' : EqDecision dms := list_eq_dec.

Local Ltac finish_lists l x :=
  elim: l => [|x xs IHds] //=; idtac + elim: x => [l d] //=; f_equal => //; by f_equal.

Lemma vl_rename_Lemma (ξ : var → var) v : rename ξ v = v.[ren ξ]
with
tm_rename_Lemma (ξ : var → var) t : rename ξ t = t.|[ren ξ]
with
dm_rename_Lemma (ξ : var → var) d : rename ξ d = d.|[ren ξ].
Proof.
  all: [> destruct v | destruct t | destruct d].
  all: rewrite /= ?up_upren_internal; f_equal => //; finish_lists l x.
Qed.

Lemma vl_ids_Lemma v : v.[ids] = v
with tm_ids_Lemma t : t.|[ids] = t
with dm_ids_Lemma d : d.|[ids] = d.
Proof.
  all: [> destruct v | destruct t | destruct d].
  all: rewrite /= ?up_id_internal; f_equal => //; finish_lists l x.
Qed.

Lemma vl_comp_rename_Lemma (ξ : var → var) (σ : var → vl) v :
  (rename ξ v).[σ] = v.[ξ >>> σ]
with
tm_comp_rename_Lemma (ξ : var → var) (σ : var → vl) t :
  (rename ξ t).|[σ] = t.|[ξ >>> σ]
with
dm_comp_rename_Lemma (ξ : var → var) (σ : var → vl) d :
  (rename ξ d).|[σ] = d.|[ξ >>> σ].
Proof.
  all: [> destruct v | destruct t | destruct d].
  all: rewrite /= 1? up_comp_ren_subst; f_equal => //; finish_lists l x.
Qed.

Lemma vl_rename_comp_Lemma (σ : var → vl) (ξ : var → var) v :
  rename ξ v.[σ] = v.[σ >>> rename ξ]
with
tm_rename_comp_Lemma (σ : var → vl) (ξ : var → var) t :
  rename ξ t.|[σ] = t.|[σ >>> rename ξ]
with
dm_rename_comp_Lemma (σ : var → vl) (ξ : var → var) d :
  rename ξ d.|[σ] = d.|[σ >>> rename ξ].
Proof.
  all: [> destruct v | destruct t | destruct d].
  all: rewrite /= ? up_comp_subst_ren_internal; f_equal => //;
    trivial using vl_rename_Lemma, vl_comp_rename_Lemma; finish_lists l x.
Qed.

Lemma vl_comp_Lemma (σ τ : var → vl) v : v.[σ].[τ] = v.[σ >> τ]
with
tm_comp_Lemma (σ τ : var → vl) t : t.|[σ].|[τ] = t.|[σ >> τ]
with
dm_comp_Lemma (σ τ : var → vl) d : d.|[σ].|[τ] = d.|[σ >> τ].
Proof.
  all: [> destruct v | destruct t | destruct d].
  all: rewrite /= ? up_comp_internal; f_equal;
    trivial using vl_rename_comp_Lemma, vl_comp_rename_Lemma; finish_lists l x.
Qed.

Instance subst_lemmas_vl : SubstLemmas vl.
Proof. split; trivial using vl_rename_Lemma, vl_ids_Lemma, vl_comp_Lemma. Qed.

Instance hsubst_lemmas_tm : HSubstLemmas vl tm.
Proof. split; trivial using tm_ids_Lemma, tm_comp_Lemma. Qed.

Instance hsubst_lemmas_dm : HSubstLemmas vl dm.
Proof. split; trivial using dm_ids_Lemma, dm_comp_Lemma. Qed.

Instance hsubst_lemmas_vls : HSubstLemmas vl vls := _.

Instance inh_label : Inhabited label := _.
Instance hsubst_lemmas_dms : HSubstLemmas vl dms := _.

(** Substitute object inside itself (to give semantics to the "self"
    variable). To use when descending under the [vobj] binder. *)
Definition selfSubst ds: dms := ds.|[vobj ds/].

Definition objLookup v (l: label) d: Prop :=
  ∃ ds, v = vobj ds ∧ (dms_lookup l (selfSubst ds)) = Some d.
Hint Unfold objLookup : core.

(* Precedence: tighter than negation and conjunction *)
Notation "v @ l ↘ d" := (objLookup v l d) (at level 74).

(** Instead of letting obj_opens_to autounfold,
    provide tactics to show it's deterministic and so on. *)

(** Rewrite v ↗ ds to vobj ds' ↗ ds. *)
Ltac simplOpen ds :=
  lazymatch goal with
  | H: ?v @ ?l ↘ ?d |- _ => inversion H as (ds & -> & _)
  end.

(** Determinacy of obj_opens_to. *)
Lemma objLookupDet v l d1 d2: v @ l ↘ d1 -> v @ l ↘ d2 -> d1 = d2.
Proof. rewrite /objLookup => *; ev. by simplify_eq. Qed.
Ltac objLookupDet :=
  lazymatch goal with
  | H1: ?v @ ?l ↘ ?d1, H2: ?v @ ?l ↘ ?d2 |- _=>
    have ?: d2 = d1 by [apply: objLookupDet]; simplify_eq
  end.

(** Instantiating iris with Dot *)
Module lang.
Import ectxi_language.

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
| st_proj v l σ w:
    v @ l ↘ dvl w →
    head_step (tproj (tv v) l) σ [] (tv w) σ []
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

Canonical Structure dlang_ectxi_lang := ectxi_language.EctxiLanguage lang.dot_lang_mixin.
Canonical Structure dlang_ectx_lang := ectxi_language.EctxLanguageOfEctxi dlang_ectxi_lang.
Canonical Structure dlang_lang := ectx_language.LanguageOfEctx dlang_ectx_lang.

Lemma hsubst_of_val (v : vl) s : (of_val v).|[s] = of_val (v.[s]).
Proof. done. Qed.

Include Sorts.
End VlSorts.
Export VlSorts.

Instance sort_dm : Sort dm := {}.

(** After instantiating Autosubst, a few binding-related syntactic definitions
    that need not their own file. *)

(** Here is a manual proof of a lemma, with explanations. *)
Lemma fv_vabs_inv_manual e n : nclosed_vl (vabs e) n → nclosed e (S n).
Proof.
  rewrite /nclosed_vl /nclosed => /= Hfv s1 s2 HsEq.

  (** From Hfv, we only learn that [e.|[up s1] = e.|[up s2]], for arbitrary [s1]
      and [s2], but substitutions in our thesis [e.|[s1] = e.|[s2]] are not of form [up ?].
      Hence, we rewrite it using [decomp_s] / [decomp_s_vl] to get a
      substitution of form [up ?], then rewrite with [e.|[up (stail s1)] =
      e.|[up (stail s2)]] (got from [Hfv]), and conclude.
      *)
  rewrite ?(decomp_s _ s1) ?(decomp_s _ s2) ?(decomp_s_vl _ s1) ?(decomp_s_vl _ s2) (eq_n_s_heads HsEq); last lia.
  injection (Hfv _ _ (eq_n_s_tails HsEq)); rewritePremises; reflexivity.
Qed.

(* Special cases needed below. *)

(* The proof of this lemma needs asimpl and hence is expensive, so we provide it
   separately. *)
Lemma fv_vobj_ds_inv l d ds n : nclosed_vl (vobj ((l, d) :: ds)) n → nclosed_vl (vobj ds) n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_vobj_d_inv l d ds n : nclosed_vl (vobj ((l, d) :: ds)) n → nclosed d (S n).
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_dtysem_inv_vs s v vs n : nclosed (dtysem (v :: vs) s) n → nclosed (dtysem vs s) n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_dtysem_inv_v s v vs n : nclosed (dtysem (v :: vs) s) n → nclosed_vl v n.
Proof. solve_inv_fv_congruence. Qed.

Hint Resolve fv_vobj_ds_inv fv_vobj_d_inv fv_dtysem_inv_v fv_dtysem_inv_vs : fvl.

(** Induction principles for syntax. *)

Section syntax_mut_rect.
  Variable Pvl : vl   → Type.
  Variable Ptm : tm   → Type.
  Variable Pdm : dm   → Type.

  Variable step_var_vl : ∀ i, Pvl (var_vl i).
  Variable step_vnat : ∀ n, Pvl (vnat n).
  Variable step_vabs : ∀ t1, Ptm t1 → Pvl (vabs t1).
  (* Original: *)
  (* Variable step_vobj : ∀ l, Pvl (vobj l). *)
  Variable step_vobj : ∀ ds, ForallT Pdm (map snd ds) → Pvl (vobj ds).

  Variable step_tv : ∀ v1, Pvl v1 → Ptm (tv v1).
  Variable step_tapp : ∀ t1 t2, Ptm t1 → Ptm t2 → Ptm (tapp t1 t2).
  Variable step_tproj : ∀ t1 l, Ptm t1 → Ptm (tproj t1 l).
  Variable step_tskip : ∀ t1, Ptm t1 → Ptm (tskip t1).

  (* Variable step_dtysyn : ∀ T1, Pty T1 → Pdm (dtysyn T1). *)
  (* Original: *)
  (* Variable step_dtysem : ∀ vsl g, Pdm (dtysem vs g). *)
  Variable step_dtysem : ∀ vs s, ForallT Pvl vs → Pdm (dtysem vs s).
  Variable step_dvl : ∀ v1, Pvl v1 → Pdm (dvl v1).

  Fixpoint vl_mut_rect v : Pvl v
  with tm_mut_rect t : Ptm t
  with dm_mut_rect d : Pdm d.
  Proof.
    (* Automation risk producing circular proofs that call right away the lemma we're proving.
       Instead we want to apply one of the [case_] arguments to perform an
       inductive step, and only then call ourselves recursively. *)
    all: [> destruct v | destruct t | destruct d].
    all:
      try match goal with
      (* Warning: add other arities as needed. *)
      | Hstep : context [?P (?c _ _ _ _)] |- ?P (?c _ _ _ _) => apply Hstep; trivial
      | Hstep : context [?P (?c _ _ _)] |- ?P (?c _ _ _) => apply Hstep; trivial
      | Hstep : context [?P (?c _ _)] |- ?P (?c _ _) => apply Hstep; trivial
      | Hstep : context [?P (?c _)] |- ?P (?c _) => apply Hstep; trivial
      | Hstep : context [?P (?c)] |- ?P (?c) => apply Hstep; trivial
      end.
    - elim: l => [|[l d] ds IHds] //=; auto.
    - elim: l => [|v vs IHxs] //=; auto.
  Qed.

  Lemma syntax_mut_rect : (∀ v, Pvl v) * (∀ t, Ptm t) * (∀ d, Pdm d).
  Proof.
    repeat split; intros; [ eapply vl_mut_rect | eapply tm_mut_rect |
      eapply dm_mut_rect].
  Qed.
End syntax_mut_rect.

Section syntax_mut_ind.
  Variable Pvl : vl   → Prop.
  Variable Ptm : tm   → Prop.
  Variable Pdm : dm   → Prop.

  Variable step_tv : ∀ v1, Pvl v1 → Ptm (tv v1).
  Variable step_tapp : ∀ t1 t2, Ptm t1 → Ptm t2 → Ptm (tapp t1 t2).
  Variable step_tproj : ∀ t1 l, Ptm t1 → Ptm (tproj t1 l).
  Variable step_tskip : ∀ t1, Ptm t1 → Ptm (tskip t1).
  Variable step_var_vl : ∀ i, Pvl (var_vl i).
  Variable step_vnat : ∀ n, Pvl (vnat n).
  Variable step_vabs : ∀ t1, Ptm t1 → Pvl (vabs t1).
  (* Original: *)
  (* Variable step_vobj : ∀ l, Pvl (vobj l). *)
  Variable step_vobj : ∀ ds, Forall Pdm (map snd ds) → Pvl (vobj ds).
  (* Variable step_dtysyn : ∀ T1, Pty T1 → Pdm (dtysyn T1). *)
  (* Original: *)
  (* Variable step_dtysem : ∀ vsl g, Pdm (dtysem vs g). *)
  Variable step_dtysem : ∀ vs s, Forall Pvl vs → Pdm (dtysem vs s).
  Variable step_dvl : ∀ v1, Pvl v1 → Pdm (dvl v1).

  Lemma syntax_mut_ind : (∀ t, Ptm t) ∧ (∀ v, Pvl v) ∧ (∀ d, Pdm d).
  Proof.
    efeed pose proof syntax_mut_rect as H; try done.
    - intros ds HdsT. apply step_vobj, ForallT_Forall, HdsT.
    - intros vs g HvsT. apply step_dtysem, ForallT_Forall, HvsT.
    - ev; split_and! ; assumption.
  Qed.

End syntax_mut_ind.

(** Induction principles for closed terms. *)

Section syntax_mut_ind_closed.
  Implicit Types (n : nat).

  Variable Pvl : vl   → nat → Prop.
  Variable Ptm : tm   → nat → Prop.
  Variable Pdm : dm   → nat → Prop.

  Variable step_var_vl : ∀ n i,
      nclosed_vl (var_vl i) n → Pvl (var_vl i) n.
  Variable step_vnat : ∀ n m,
      nclosed_vl (vnat m) n → Pvl (vnat m) n.
  Variable step_vabs : ∀ n t1,
      nclosed t1 (S n) →
      nclosed_vl (vabs t1) n →
      Ptm t1 (S n) → Pvl (vabs t1) n.
  Variable step_vobj : ∀ n ds,
      nclosed ds (S n) → nclosed_vl (vobj ds) n →
      Forall (flip Pdm (S n)) (map snd ds) →
      Pvl (vobj ds) n.

  Variable step_tv : ∀ n v1,
      nclosed_vl v1 n → nclosed (tv v1) n →
      Pvl v1 n → Ptm (tv v1) n.
  Variable step_tapp : ∀ n t1 t2,
      nclosed t1 n → nclosed t2 n → nclosed (tapp t1 t2) n →
      Ptm t1 n → Ptm t2 n → Ptm (tapp t1 t2) n.
  Variable step_tproj : ∀ n t1 l,
      nclosed t1 n → nclosed (tproj t1 l) n →
      Ptm t1 n → Ptm (tproj t1 l) n.
  Variable step_tskip : ∀ n t1,
      nclosed t1 n → nclosed (tskip t1) n →
      Ptm t1 n → Ptm (tskip t1) n.

  (* Variable step_dtysyn : ∀ n T1,
      nclosed T1 n →
      nclosed (dtysyn T1) n →
      Pty T1 n → Pdm (dtysyn T1) n. *)
  Variable step_dtysem : ∀ n vs s,
      nclosed vs n → nclosed (dtysem vs s) n →
      Forall (flip Pvl n) vs → Pdm (dtysem vs s) n.
  Variable step_dvl : ∀ n v1,
      nclosed_vl v1 n → nclosed (dvl v1) n →
      Pvl v1 n → Pdm (dvl v1) n.

  Fixpoint nclosed_vl_mut_ind n v : nclosed_vl v n → Pvl v n
  with     nclosed_tm_mut_ind n t : nclosed t n → Ptm t n
  with     nclosed_dm_mut_ind n d : nclosed d n → Pdm d n.
  Proof.
    (* Automation risk producing circular proofs that call right away the lemma we're proving.
       Instead we want to apply one of the [case_] arguments to perform an
       inductive step, and only then call ourselves recursively. *)
    all: [> destruct v | destruct t | destruct d].
    all: intro Hcl; let byEapply p := efeed p using (fun q => apply q) by (eauto 2; eauto 1 with fv)
    in
      match goal with
      (* Warning: add other arities as needed. *)
      | Hstep : context [?P (?c _ _ _) _] |- ?P (?c ?a1 ?a2 ?a3) _ => byEapply (Hstep n a1 a2 a3)
      | Hstep : context [?P (?c _ _) _] |- ?P (?c ?a1 ?a2) _ => byEapply (Hstep n a1 a2)
      | Hstep : context [?P (?c _) _] |- ?P (?c ?a1) _ => byEapply (Hstep n a1)
      | Hstep : context [?P (?c) _] |- ?P (?c) _ => byEapply (Hstep n)
      end.
    - elim: l Hcl => [|[l d] ds IHds] Hcl /=; constructor => /=; eauto 3 with fvl.
    - elim: l Hcl => [|v vs IHxs]; constructor => /=; eauto 3 with fvl.
  Qed.

  Lemma nclosed_syntax_mut_ind : (∀ v n, nclosed_vl v n → Pvl v n) ∧
    (∀ t n, nclosed t n → Ptm t n) ∧ (∀ d n, nclosed d n → Pdm d n).
  Proof.
    repeat split; intros.
    - exact: nclosed_vl_mut_ind.
    - exact: nclosed_tm_mut_ind.
    - exact: nclosed_dm_mut_ind.
  Qed.
End syntax_mut_ind_closed.
