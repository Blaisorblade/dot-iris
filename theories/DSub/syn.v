From D Require Export prelude.
From D Require Import asubst_base.
From iris.program_logic Require ectx_language ectxi_language.


Inductive tm : Type :=
  | tv : vl_ -> tm
  | tapp : tm -> tm -> tm
  | tskip : tm -> tm
 with vl_ : Type :=
  | var_vl : var -> vl_
  | vnat : nat -> vl_
  | vabs : tm -> vl_
  | vty : ty -> vl_
  | vstamp : list vl_ -> stamp -> vl_
 with ty : Type :=
  | TTop : ty
  | TBot : ty
  (* | TAnd : ty -> ty -> ty *)
  (* | TOr : ty -> ty -> ty *)
  | TLater : ty -> ty
  | TAll : ty -> ty -> ty
  (* | TMu : ty -> ty *)
  | TTMem : ty -> ty -> ty
  | TSel : vl_ -> ty
  | TNat : ty.

Definition vl := vl_.

Definition vls := list vl.
Definition ctx := list ty.

Implicit Types
         (L T U : ty) (v : vl) (t : tm)
         (Γ : ctx).

Instance inh_ty : Inhabited ty := populate TNat.
Instance inh_vl : Inhabited vl := populate (vnat 0).
Instance inh_tm : Inhabited tm := populate (tv inhabitant).

Instance ids_vl : Ids vl := var_vl.

Instance inj_ids : Inj (=) (=@{vl}) ids.
Proof. by move=>??[]. Qed.

Instance ids_tm : Ids tm := inh_ids.
Instance ids_ty : Ids ty := inh_ids.
Instance ids_vls : Ids vls := _.
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
  | var_vl x => var_vl (sb x)
  | vnat n => vnat n
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
  | TNat => TNat
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
  | var_vl x => sb x
  | vnat n => vnat n
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
  | TNat => TNat
  end.

Instance subst_vl : Subst vl := vl_subst.
Instance hsubst_tm : HSubst vl tm := tm_hsubst.
Instance hsubst_ty : HSubst vl ty := ty_hsubst.

Lemma vl_eq_dec v1 v2 : Decision (v1 = v2)
with
tm_eq_dec t1 t2 : Decision (t1 = t2)
with
ty_eq_dec T1 T2 : Decision (T1 = T2).
Proof.
   all: rewrite /Decision; decide equality;
       try (apply vl_eq_dec || apply tm_eq_dec || apply ty_eq_dec ||
            apply @list_eq_dec ||
            apply nat_eq_dec || apply positive_eq_dec); auto.
Qed.

Instance vl_eq_dec' : EqDecision vl := vl_eq_dec.
Instance tm_eq_dec' : EqDecision tm := tm_eq_dec.
Instance ty_eq_dec' : EqDecision ty := ty_eq_dec.
Instance vls_eq_dec' : EqDecision vls := list_eq_dec.

Local Ltac finish_lists l x :=
  elim: l => [|x xs IHds] //=; by f_equal.

Lemma vl_rename_Lemma (ξ : var → var) v : rename ξ v = v.[ren ξ]
with
tm_rename_Lemma (ξ : var → var) t : rename ξ t = t.|[ren ξ]
with
ty_rename_Lemma (ξ : var → var) T : rename ξ T = T.|[ren ξ].
Proof.
  all: destruct 0; rewrite /= ?up_upren_internal; f_equal => //; finish_lists l x.
Qed.

Lemma vl_ids_Lemma v : v.[ids] = v
with
tm_ids_Lemma t : t.|[ids] = t
with
ty_ids_Lemma T : T.|[ids] = T.
Proof.
  all: destruct 0; rewrite /= ?up_id_internal; f_equal => //; finish_lists l x.
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
  all: destruct 0; rewrite /= 1? up_comp_ren_subst; f_equal => //; finish_lists l x.
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
  all: destruct 0; rewrite /= ? up_comp_subst_ren_internal; f_equal => //;
    auto using vl_rename_Lemma, vl_comp_rename_Lemma; finish_lists l x.
Qed.

Lemma vl_comp_Lemma (σ τ : var → vl) v : v.[σ].[τ] = v.[σ >> τ]
with
tm_comp_Lemma (σ τ : var → vl) t : t.|[σ].|[τ] = t.|[σ >> τ]
with
ty_comp_Lemma (σ τ : var → vl) T : T.|[σ].|[τ] = T.|[σ >> τ].
Proof.
  all: destruct 0; rewrite /= ? up_comp_internal; f_equal;
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

Definition of_val: vl -> tm := tv.

Inductive ectx_item :=
| AppLCtx (e2: tm)
| AppRCtx (v1: vl)
| SkipCtx.

Definition fill_item (Ki : ectx_item) (e : tm) : tm :=
  match Ki with
  | AppLCtx e2 => tapp e e2
  | AppRCtx v1 => tapp (tv v1) e
  | TSkipCtx => tskip e
  end.

Definition state := unit.
Definition observation := unit.

Inductive head_step : tm -> state -> list observation -> tm -> state -> list tm -> Prop :=
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

Include Sorts.

Instance sort_tm : Sort tm := {}.
Instance sort_ty : Sort ty := {}.

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

(** Induction principles for syntax. *)

(* Using a Section is a trick taken from CPDT, but there bodies are hand-written.
   The rest is written by taking Coq's generated recursion principles and doing
   lots of regexp search-n-replace.
 *)

Section syntax_mut_rect.
  Variable Ptm : tm → Type.
  Variable Pvl : vl → Type.
  Variable Pty : ty → Type.

  Variable step_tv : ∀ v1, Pvl v1 → Ptm (tv v1).
  Variable step_tapp : ∀ t1 t2, Ptm t1 → Ptm t2 → Ptm (tapp t1 t2).
  Variable step_tskip : ∀ t1, Ptm t1 → Ptm (tskip t1).
  Variable step_var_vl : ∀ i, Pvl (var_vl i).
  Variable step_vnat : ∀ n, Pvl (vnat n).
  Variable step_vabs : ∀ t1, Ptm t1 → Pvl (vabs t1).
  Variable step_vty : ∀ T1, Pty T1 → Pvl (vty T1).
  Variable step_vstamp : ∀ vs s, ForallT Pvl vs → Pvl (vstamp vs s).
  Variable step_TTop : Pty TTop.
  Variable step_TBot : Pty TBot.
  Variable step_TLater : ∀ T1, Pty T1 → Pty (TLater T1).
  Variable step_TALl : ∀ T1 T2, Pty T1 → Pty T2 → Pty (TAll T1 T2).
  Variable step_TTMem : ∀ T1 T2, Pty T1 → Pty T2 → Pty (TTMem T1 T2).
  Variable step_TSel : ∀ v1, Pvl v1 → Pty (TSel v1).
  Variable step_TNat : Pty TNat.

  Fixpoint tm_mut_rect t : Ptm t
  with vl_mut_rect v : Pvl v
  with ty_mut_rect T : Pty T.
  Proof.
    (* Automation risk producing circular proofs that call right away the lemma we're proving.
       Instead we want to apply one of the [case_] arguments to perform an
       inductive step, and only then call ourselves recursively. *)
    all: destruct 0;
      match goal with
      (* Warning: add other arities as needed. *)
      | Hstep : context [?P (?c _ _ _)] |- ?P (?c _ _ _) => apply Hstep; trivial
      | Hstep : context [?P (?c _ _)] |- ?P (?c _ _) => apply Hstep; trivial
      | Hstep : context [?P (?c _)] |- ?P (?c _) => apply Hstep; trivial
      | Hstep : context [?P (?c)] |- ?P (?c) => apply Hstep; trivial
      end.
    induction l; auto.
  Qed.

  Lemma syntax_mut_rect : (∀ t, Ptm t) * (∀ v, Pvl v) * (∀ T, Pty T).
  Proof.
    repeat split; intros.
    - eapply tm_mut_rect.
    - eapply vl_mut_rect.
    - eapply ty_mut_rect.
  Qed.
End syntax_mut_rect.

Section syntax_mut_ind.
  Variable Ptm : tm → Prop.
  Variable Pvl : vl → Prop.
  Variable Pty : ty → Prop.

  Variable step_tv : ∀ v1, Pvl v1 → Ptm (tv v1).
  Variable step_tapp : ∀ t1 t2, Ptm t1 → Ptm t2 → Ptm (tapp t1 t2).
  Variable step_tskip : ∀ t1, Ptm t1 → Ptm (tskip t1).
  Variable step_var_vl : ∀ i, Pvl (var_vl i).
  Variable step_vnat : ∀ n, Pvl (vnat n).
  Variable step_vabs : ∀ t1, Ptm t1 → Pvl (vabs t1).
  Variable step_vty : ∀ T1, Pty T1 → Pvl (vty T1).
  (** Beware here in Prop we use Forall, not ForallT! *)
  Variable step_vstamp : ∀ vs s, Forall Pvl vs → Pvl (vstamp vs s).
  Variable step_TTop : Pty TTop.
  Variable step_TBot : Pty TBot.
  Variable step_TLater : ∀ T1, Pty T1 → Pty (TLater T1).
  Variable step_TALl : ∀ T1 T2, Pty T1 → Pty T2 → Pty (TAll T1 T2).
  Variable step_TTMem : ∀ T1 T2, Pty T1 → Pty T2 → Pty (TTMem T1 T2).
  Variable step_TSel : ∀ v1, Pvl v1 → Pty (TSel v1).
  Variable step_TNat : Pty TNat.

  Lemma syntax_mut_ind : (∀ t, Ptm t) ∧ (∀ v, Pvl v) ∧ (∀ T, Pty T).
  Proof.
    efeed pose proof syntax_mut_rect as H; try done.
    - intros vs g HvsT. apply step_vstamp, ForallT_Forall, HvsT.
    - ev; split_and! ; assumption.
  Qed.
End syntax_mut_ind.

(** Induction principles for closed terms. *)

Section syntax_mut_ind_closed.
  Variable Ptm : tm → nat → Prop.
  Variable Pvl : vl → nat → Prop.
  Variable Pty : ty → nat → Prop.

  Implicit Types (n : nat).

  Variable step_tv : ∀ n v1,
      nclosed_vl v1 n → nclosed (tv v1) n → Pvl v1 n → Ptm (tv v1) n.
  Variable step_tapp : ∀ n t1 t2,
      nclosed t1 n → nclosed t2 n → nclosed (tapp t1 t2) n →
      Ptm t1 n → Ptm t2 n → Ptm (tapp t1 t2) n.
  Variable step_tskip : ∀ n t1,
      nclosed t1 n → nclosed (tskip t1) n →
      Ptm t1 n → Ptm (tskip t1) n.
  Variable step_var_vl : ∀ n i,
      nclosed_vl (var_vl i) n → Pvl (var_vl i) n.
  Variable step_vnat : ∀ n m,
      nclosed_vl (vnat m) n → Pvl (vnat m) n.
  Variable step_vabs : ∀ n t1,
      nclosed t1 (S n) →
      nclosed_vl (vabs t1) n →
      Ptm t1 (S n) → Pvl (vabs t1) n.

  Variable step_vty : ∀ n T1,
      nclosed T1 n → nclosed_vl (vty T1) n →
      Pty T1 n → Pvl (vty T1) n.
  (** Beware here in Prop we use Forall, not ForallT! *)
  Variable step_vstamp : ∀ n vs s,
      nclosed vs n → nclosed_vl (vstamp vs s) n →
      Forall (flip Pvl n) vs → Pvl (vstamp vs s) n.
  Variable step_TTop : ∀ n,
      nclosed TTop n →
      Pty TTop n.
  Variable step_TBot : ∀ n,
      nclosed TBot n →
      Pty TBot n.
  Variable step_TLater : ∀ n T1,
      nclosed T1 n → nclosed (TLater T1) n →
      Pty T1 n → Pty (TLater T1) n.
  Variable step_TAll : ∀ n T1 T2,
      nclosed T1 n → nclosed T2 (S n) → nclosed (TAll T1 T2) n →
      Pty T1 n → Pty T2 (S n) → Pty (TAll T1 T2) n.
  Variable step_TTMem : ∀ n T1 T2,
      nclosed T1 n → nclosed T2 n → nclosed (TTMem T1 T2) n →
      Pty T1 n → Pty T2 n → Pty (TTMem T1 T2) n.
  Variable step_TSel : ∀ n v1,
      nclosed_vl v1 n → nclosed (TSel v1) n →
      Pvl v1 n → Pty (TSel v1) n.
  Variable step_TNat : ∀ n,
      nclosed TNat n →
      Pty TNat n.

  Fixpoint nclosed_tm_mut_ind n t : nclosed t n → Ptm t n
  with     nclosed_vl_mut_ind n v : nclosed_vl v n → Pvl v n
  with     nclosed_ty_mut_ind n T : nclosed T n → Pty T n.
  Proof.
    (* Automation risk producing circular proofs that call right away the lemma we're proving.
       Instead we want to apply one of the [case_] arguments to perform an
       inductive step, and only then call ourselves recursively. *)
    all: destruct 0; intro Hcl.
    all: let byEapply p := efeed p using (fun q => apply q) by (eauto 2; eauto 1 with fv)
    in
      match goal with
      (* Warning: add other arities as needed. *)
      | Hstep : context [?P (?c _ _ _) _] |- ?P (?c ?a1 ?a2 ?a3) _ => byEapply (Hstep n a1 a2 a3)
      | Hstep : context [?P (?c _ _) _] |- ?P (?c ?a1 ?a2) _ => byEapply (Hstep n a1 a2)
      | Hstep : context [?P (?c _) _] |- ?P (?c ?a1) _ => byEapply (Hstep n a1)
      | Hstep : context [?P (?c) _] |- ?P (?c) _ => byEapply (Hstep n)
      end.
    - induction l as [| a l]; constructor => /=; eauto 2 with fv.
  Qed.

  Lemma nclosed_syntax_mut_ind : (∀ t n, nclosed t n → Ptm t n) ∧ (∀ v n, nclosed_vl v n → Pvl v n) ∧ (∀ T n, nclosed T n → Pty T n).
  Proof.
    repeat split; intros.
    - exact: nclosed_tm_mut_ind.
    - exact: nclosed_vl_mut_ind.
    - exact: nclosed_ty_mut_ind.
  Qed.
End syntax_mut_ind_closed.
