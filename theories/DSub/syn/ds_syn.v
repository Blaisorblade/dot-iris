From D Require Export prelude.
From D Require Import asubst_intf asubst_base.
From iris.program_logic Require ectx_language ectxi_language.

Set Suggest Proof Using.
Set Default Proof Using "Type*".

(** This module is included right away. Its only point is asserting explicitly
    what interface it implements. *)
Module Export VlSorts <: VlSortsFullSig.
Import ASubstLangDefUtils.

Inductive tm : Type :=
  | tv : vl_ → tm
  | tapp : tm → tm → tm
  | tskip : tm → tm
 with vl_ : Type :=
  | vvar : var → vl_
  | vint : Z → vl_
  | vabs : tm → vl_
  | vty : ty → vl_
  | vstamp : list vl_ → stamp → vl_
 with ty : Type :=
  | TTop : ty
  | TBot : ty
  (* | TAnd : ty → ty → ty *)
  (* | TOr : ty → ty → ty *)
  | TLater : ty → ty
  | TAll : ty → ty → ty
  (* | TMu : ty → ty *)
  | TTMem : ty → ty → ty
  | TSel : vl_ → ty
  | TInt : ty.

Definition vl := vl_.

Definition ctx := list ty.

Implicit Types
         (L T U : ty) (v : vl) (t : tm)
         (Γ : ctx).

Instance inh_ty : Inhabited ty := populate TInt.
Instance inh_vl : Inhabited vl := populate (vint 0).
Instance inh_tm : Inhabited tm := populate (tv inhabitant).

Instance ids_vl : Ids vl := vvar.

Instance inj_ids : Inj (=) (=@{vl}) ids.
Proof. by move=>??[]. Qed.

Instance ids_tm : Ids tm := inh_ids.
Instance ids_ty : Ids ty := inh_ids.
Instance ids_ctx : Ids ctx := _.

Fixpoint tm_rename (sb : var → var) t : tm :=
  let a := tm_rename : Rename tm in
  let b := vl_rename : Rename vl in
  match t with
  | tv v => tv (rename sb v)
  | tapp t1 t2 => tapp (rename sb t1) (rename sb t2)
  | tskip t => tskip (rename sb t)
  end
with
vl_rename (sb : var → var) v : vl :=
  let a := tm_rename : Rename tm in
  let b := vl_rename : Rename vl in
  let c := ty_rename : Rename ty in
  match v with
  | vvar x => vvar (sb x)
  | vint n => vint n
  | vabs t => vabs (rename (upren sb) t)
  | vty T => vty (rename sb T)
  | vstamp vs s => vstamp (rename sb vs) s
  end
with
ty_rename (sb : var → var) T : ty :=
  let a := ty_rename : Rename ty in
  let b := vl_rename : Rename vl in
  match T with
  | TTop => TTop
  | TBot => TBot
  (* | TAnd T1 T2 => TAnd (rename sb T1) (rename sb T2) *)
  (* | TOr T1 T2 => TOr (rename sb T1) (rename sb T2) *)
  | TLater T => TLater (rename sb T)
  | TAll T1 T2 => TAll (rename sb T1) (rename (upren sb) T2)
  (* | TMu T => TMu (rename (upren sb) T) *)
  | TTMem T1 T2 => TTMem (rename sb T1) (rename sb T2)
  | TSel v => TSel (rename sb v)
  | TInt => TInt
  end.

Instance rename_tm : Rename tm := tm_rename.
Instance rename_vl : Rename vl := vl_rename.
Instance rename_ty : Rename ty := ty_rename.

Fixpoint tm_hsubst (sb : var → vl) t : tm :=
  let a := tm_hsubst : HSubst vl tm in
  let b := vl_subst : Subst vl in
  match t with
  | tv v => tv (subst sb v)
  | tapp t1 t2 => tapp (hsubst sb t1) (hsubst sb t2)
  | tskip t => tskip (hsubst sb t)
  end
with
vl_subst (sb : var → vl) v : vl :=
  let a := tm_hsubst : HSubst vl tm in
  let b := vl_subst : Subst vl in
  let c := ty_hsubst : HSubst vl ty in
  match v with
  | vvar x => sb x
  | vint n => vint n
  | vabs t => vabs (hsubst (up sb) t)
  | vty T => vty (hsubst sb T)
  | vstamp vs s => vstamp (hsubst sb vs) s
  end
with
ty_hsubst (sb : var → vl) T : ty :=
  let a := ty_hsubst : HSubst vl ty in
  let b := vl_subst : Subst vl in
  match T with
  | TTop => TTop
  | TBot => TBot
  (* | TAnd T1 T2 => TAnd (hsubst sb T1) (hsubst sb T2) *)
  (* | TOr T1 T2 => TOr (hsubst sb T1) (hsubst sb T2) *)
  | TLater T => TLater (hsubst sb T)
  | TAll T1 T2 => TAll (hsubst sb T1) (hsubst (up sb) T2)
  (* | TMu T => TMu (hsubst (up sb) T) *)
  | TTMem T1 T2 => TTMem (hsubst sb T1) (hsubst sb T2)
  | TSel v => TSel (subst sb v)
  | TInt => TInt
  end.

Instance subst_vl : Subst vl := vl_subst.
Instance hsubst_tm : HSubst vl tm := tm_hsubst.
Instance hsubst_ty : HSubst vl ty := ty_hsubst.

Lemma vl_eq_dec v1 v2 : Decision (v1 = v2)
with
tm_eq_dec t1 t2 : Decision (t1 = t2)
with
ty_eq_dec T1 T2 : Decision (T1 = T2).
Proof. all: rewrite /Decision; decide equality; solve_decision. Defined.

Instance vl_eq_dec' : EqDecision vl := vl_eq_dec.
Instance tm_eq_dec' : EqDecision tm := tm_eq_dec.
Instance ty_eq_dec' : EqDecision ty := ty_eq_dec.

Local Ltac finish_lists l x :=
  elim: l => [|x xs IHds] //=; by f_equal.

Lemma up_upren_vl (ξ : var → var): up (ren ξ) =@{var → vl} ren (upren ξ).
Proof. exact: up_upren_internal. Qed.

Lemma vl_rename_Lemma (ξ : var → var) v : rename ξ v = v.[ren ξ]
with
tm_rename_Lemma (ξ : var → var) t : rename ξ t = t.|[ren ξ]
with
ty_rename_Lemma (ξ : var → var) T : rename ξ T = T.|[ren ξ].
Proof.
  all: [> destruct v | destruct t | destruct T].
  all: rewrite /= ?up_upren_vl; f_equal => //; finish_lists l x.
Qed.

Lemma vl_ids_Lemma v : v.[ids] = v
with
tm_ids_Lemma t : t.|[ids] = t
with
ty_ids_Lemma T : T.|[ids] = T.
Proof.
  all: [> destruct v | destruct t | destruct T].
  all: rewrite /= ?up_id_internal; f_equal => //; finish_lists l x.
Qed.

Lemma vl_comp_rename_Lemma (ξ : var → var) (σ : var → vl) v :
  (rename ξ v).[σ] = v.[ξ >>> σ]
with
tm_comp_rename_Lemma (ξ : var → var) (σ : var → vl) t :
  (rename ξ t).|[σ] = t.|[ξ >>> σ]
with
ty_comp_rename_Lemma (ξ : var → var) (σ : var → vl) T :
  (rename ξ T).|[σ] = T.|[ξ >>> σ].
Proof.
  all: [> destruct v | destruct t | destruct T].
  all: rewrite /= 1? up_comp_ren_subst; f_equal => //; finish_lists l x.
Qed.

Lemma vl_rename_comp_Lemma (σ : var → vl) (ξ : var → var) v :
  rename ξ v.[σ] = v.[σ >>> rename ξ]
with
tm_rename_comp_Lemma (σ : var → vl) (ξ : var → var) t :
  rename ξ t.|[σ] = t.|[σ >>> rename ξ]
with
ty_rename_comp_Lemma (σ : var → vl) (ξ : var → var) T :
  rename ξ T.|[σ] = T.|[σ >>> rename ξ].
Proof.
  all: [> destruct v | destruct t | destruct T].
  all: rewrite /= ? up_comp_subst_ren_internal; f_equal => //;
    auto using vl_rename_Lemma, vl_comp_rename_Lemma; finish_lists l x.
Qed.

Lemma vl_comp_Lemma (σ τ : var → vl) v : v.[σ].[τ] = v.[σ >> τ]
with
tm_comp_Lemma (σ τ : var → vl) t : t.|[σ].|[τ] = t.|[σ >> τ]
with
ty_comp_Lemma (σ τ : var → vl) T : T.|[σ].|[τ] = T.|[σ >> τ].
Proof.
  all: [> destruct v | destruct t | destruct T].
  all: rewrite /= ? up_comp_internal; f_equal;
    auto using vl_rename_comp_Lemma, vl_comp_rename_Lemma; finish_lists l x.
Qed.

Instance subst_lemmas_vl : SubstLemmas vl.
Proof.
  split; auto using vl_rename_Lemma, vl_ids_Lemma, vl_comp_Lemma.
Qed.

Instance hsubst_lemmas_tm : HSubstLemmas vl tm.
Proof.
  split; auto using tm_ids_Lemma, tm_comp_Lemma.
Qed.

Instance hsubst_lemmas_ty : HSubstLemmas vl ty.
Proof.
  split; auto using ty_ids_Lemma, ty_comp_Lemma.
Qed.

Instance hsubst_lemmas_ctx : HSubstLemmas vl ctx := _.

(** Instantiating iris with DSub *)
Module lang.
Import ectxi_language.

Definition to_val (t: tm) : option vl :=
  match t with
  | tv v => Some v
  | _ => None
  end.

Definition of_val: vl → tm := tv.

Inductive ectx_item :=
| AppLCtx (e2: tm)
| AppRCtx (v1: vl)
| SkipCtx.

Definition fill_item (Ki : ectx_item) (e : tm) : tm :=
  match Ki with
  | AppLCtx e2 => tapp e e2
  | AppRCtx v1 => tapp (tv v1) e
  | SkipCtx => tskip e
  end.

Inductive head_step : tm → unit → list unit → tm → unit → list tm → Prop :=
| st_beta t1 v2 σ:
    head_step (tapp (tv (vabs t1)) (tv v2)) σ [] (t1.|[v2/]) σ []
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

Lemma dsub_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
  split; eauto using of_to_val, val_stuck, fill_item_val,
    fill_item_no_val_inj, head_ctx_step_val with typeclass_instances.
Qed.

End lang.

Export lang.

Canonical Structure dlang_ectxi_lang := ectxi_language.EctxiLanguage lang.dsub_lang_mixin.
Canonical Structure dlang_ectx_lang := ectxi_language.EctxLanguageOfEctxi dlang_ectxi_lang.
Canonical Structure dlang_lang := ectx_language.LanguageOfEctx dlang_ectx_lang.

Lemma hsubst_of_val (v : vl) s : (of_val v).|[s] = of_val (v.[s]).
Proof. done. Qed.

Include Sorts.
End VlSorts.

Instance sort_ty : Sort ty := {}.

(** Induction principles for syntax. *)

(* Using a Section is a trick taken from CPDT, but there bodies are hand-written.
   The rest is written by taking Coq's generated recursion principles and doing
   lots of regexp search-n-replace.
 *)

Section syntax_mut_ind.
  Variable Ptm : tm → Prop.
  Variable Pvl : vl → Prop.
  Variable Pty : ty → Prop.

  Variable step_tv : ∀ v1, Pvl v1 → Ptm (tv v1).
  Variable step_tapp : ∀ t1 t2, Ptm t1 → Ptm t2 → Ptm (tapp t1 t2).
  Variable step_tskip : ∀ t1, Ptm t1 → Ptm (tskip t1).
  Variable step_var_vl : ∀ i, Pvl (vvar i).
  Variable step_vint : ∀ n, Pvl (vint n).
  Variable step_vabs : ∀ t1, Ptm t1 → Pvl (vabs t1).
  Variable step_vty : ∀ T1, Pty T1 → Pvl (vty T1).
  Variable step_vstamp : ∀ vs s, Forall Pvl vs → Pvl (vstamp vs s).
  Variable step_TTop : Pty TTop.
  Variable step_TBot : Pty TBot.
  Variable step_TLater : ∀ T1, Pty T1 → Pty (TLater T1).
  Variable step_TALl : ∀ T1 T2, Pty T1 → Pty T2 → Pty (TAll T1 T2).
  Variable step_TTMem : ∀ T1 T2, Pty T1 → Pty T2 → Pty (TTMem T1 T2).
  Variable step_TSel : ∀ v1, Pvl v1 → Pty (TSel v1).
  Variable step_TInt : Pty TInt.

  Fixpoint tm_mut_ind t : Ptm t
  with vl_mut_ind v : Pvl v
  with ty_mut_ind T : Pty T.
  Proof.
    (* Automation risk producing circular proofs that call right away the lemma we're proving.
       Instead we want to apply one of the [case_] arguments to perform an
       inductive step, and only then call ourselves recursively. *)
    all: [> destruct t | destruct v | destruct T].
    all:
      match goal with
      (* Warning: add other arities as needed. *)
      | Hstep : context [?P (?c _ _ _)] |- ?P (?c _ _ _) => apply Hstep; trivial
      | Hstep : context [?P (?c _ _)] |- ?P (?c _ _) => apply Hstep; trivial
      | Hstep : context [?P (?c _)] |- ?P (?c _) => apply Hstep; trivial
      | Hstep : context [?P (?c)] |- ?P (?c) => apply Hstep; trivial
      end.
    induction l; auto.
  Qed.

  Lemma syntax_mut_ind : (∀ t, Ptm t) ∧ (∀ v, Pvl v) ∧ (∀ T, Pty T).
  Proof.
    repeat split; intros.
    - eapply tm_mut_ind.
    - eapply vl_mut_ind.
    - eapply ty_mut_ind.
  Qed.
End syntax_mut_ind.
