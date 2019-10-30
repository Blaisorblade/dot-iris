From D Require Export prelude.
From D Require Import asubst_intf asubst_base.
From iris.program_logic Require ectx_language ectxi_language.
From D.HkDot.syn Require Export syn.
(* From stdpp Require Import strings. *)

Inductive path : Type :=
  | pv : vl_ -> path
  | pself : path -> label -> path.

Inductive ty : Type :=
  | TTop : ty
  | TBot : ty
  | TAnd (T1 T2 : ty)
  | TOr (T1 T2 : ty)
  | TLater (T1 : ty)
  | TAll (T1 T2 : ty)
  | TMu (T1 : ty)
  | TVMem (l : label) (T1 : ty)
  | TTMem (l : label) (T1 T2 : ty)
  | TSel (p : path) (l : label)
  | TNat.

Definition ctx := list ty.
Bind Scope ty_scope with ty.
Delimit Scope ty_scope with ty.

Implicit Types (v : vl) (t : tm) (d : dm) (ds : dms) (vs : vls) (l : label).
Implicit Types (T : ty) (p : path) (Γ : ctx).

Definition label_of_ty T : option label :=
  match T with
  | TTMem l _ _ => Some l
  | TVMem l _ => Some l
  | _ => None
  end.

Fixpoint plength p : nat :=
  match p with
  | pv _ => 0
  | pself p _ => S (plength p)
  end.

Instance inh_pth : Inhabited path := populate (pv inhabitant).
Instance inh_ty : Inhabited ty := populate TNat.

Instance ids_pth : Ids path := inh_ids.
Instance ids_ty : Ids ty := inh_ids.
Instance ids_ctx : Ids ctx := _.

Fixpoint path_rename (sb : var → var) p : path :=
  let a := path_rename : Rename path in
  match p with
  | pv v => pv (rename sb v)
  | pself p l => pself (rename sb p) l
  end.
Instance rename_pth : Rename path := path_rename.

Fixpoint ty_rename (sb : var → var) T : ty :=
  let a := ty_rename : Rename ty in
  match T with
  | TTop => TTop
  | TBot => TBot
  | TAnd T1 T2 => TAnd (rename sb T1) (rename sb T2)
  | TOr T1 T2 => TOr (rename sb T1) (rename sb T2)
  | TLater T => TLater (rename sb T)
  | TAll T1 T2 => TAll (rename sb T1) (rename (upren sb) T2)
  | TMu T => TMu (rename (upren sb) T)
  | TVMem l T => TVMem l (rename sb T)
  | TTMem l T1 T2 => TTMem l (rename sb T1) (rename sb T2)
  | TSel p l => TSel (rename sb p) l
  | TNat => TNat
  end.
Instance rename_ty : Rename ty := ty_rename.

Fixpoint path_hsubst (sb : var → vl) p : path :=
  let a := path_hsubst : HSubst vl path in
  match p with
  | pv v => pv (subst sb v)
  | pself p l => pself (hsubst sb p) l
  end.
Instance hsubst_pth : HSubst vl path := path_hsubst.

Fixpoint ty_hsubst (sb : var → vl) T : ty :=
  let a := ty_hsubst : HSubst vl ty in
  match T with
  | TTop => TTop
  | TBot => TBot
  | TAnd T1 T2 => TAnd (hsubst sb T1) (hsubst sb T2)
  | TOr T1 T2 => TOr (hsubst sb T1) (hsubst sb T2)
  | TLater T => TLater (hsubst sb T)
  | TAll T1 T2 => TAll (hsubst sb T1) (hsubst (up sb) T2)
  | TMu T => TMu (hsubst (up sb) T)
  | TVMem l T => TVMem l (hsubst sb T)
  | TTMem l T1 T2 => TTMem l (hsubst sb T1) (hsubst sb T2)
  | TSel p l => TSel (hsubst sb p) l
  | TNat => TNat
  end.
Instance hsubst_ty : HSubst vl ty := ty_hsubst.

From stdpp Require Import strings.
Lemma path_eq_dec p1 p2 : Decision (p1 = p2).
Proof.
   rewrite /Decision; decide equality; [apply vl_eq_dec | apply string_eq_dec]; auto.
Qed.
Instance path_eq_dec' : EqDecision path := path_eq_dec.

Lemma ty_eq_dec T1 T2 : Decision (T1 = T2).
Proof.
   rewrite /Decision; decide equality; first [apply string_eq_dec | apply path_eq_dec]; auto.
Qed.
Instance ty_eq_dec' : EqDecision ty := ty_eq_dec.

Lemma path_rename_Lemma (ξ : var → var) p : rename ξ p = p.|[ren ξ].
Proof.
  elim: p => [^~s]; rewrite /= ?up_upren_internal; f_equal;
    trivial using vl_rename_Lemma.
Qed.

Lemma ty_rename_Lemma (ξ : var → var) T : rename ξ T = T.|[ren ξ].
Proof.
  elim: T ξ => [^~s] ξ; rewrite /= ?up_upren_internal; f_equal;
    trivial using path_rename_Lemma.
Qed.

Lemma path_ids_Lemma p : p.|[ids] = p.
Proof.
  elim: p => [^~s]; rewrite /= ?up_id_internal; f_equal; trivial using vl_ids_Lemma.
Qed.
Lemma ty_ids_Lemma T : T.|[ids] = T.
Proof.
  elim: T => [^~s]; rewrite /= ?up_id_internal; f_equal; trivial using path_ids_Lemma.
Qed.

Lemma path_comp_rename_Lemma (ξ : var → var) (σ : var → vl) p :
  (rename ξ p).|[σ] = p.|[ξ >>> σ].
Proof.
  elim: p => [^~s]; rewrite /= 1? up_comp_ren_subst; f_equal; trivial using vl_comp_rename_Lemma.
Qed.

Lemma ty_comp_rename_Lemma (ξ : var → var) (σ : var → vl) T :
  (rename ξ T).|[σ] = T.|[ξ >>> σ].
Proof.
  elim: T ξ σ =>[^~s] ξ σ; rewrite /= 1? up_comp_ren_subst; f_equal;
    trivial using path_comp_rename_Lemma.
Qed.

Lemma path_rename_comp_Lemma (σ : var → vl) (ξ : var → var) p :
  rename ξ p.|[σ] = p.|[σ >>> rename ξ].
Proof.
  elim: p =>[^~s]; rewrite /= ? up_comp_subst_ren_internal; f_equal;
    trivial using vl_rename_Lemma, vl_comp_rename_Lemma, vl_rename_comp_Lemma.
Qed.
Lemma ty_rename_comp_Lemma (σ : var → vl) (ξ : var → var) T :
  rename ξ T.|[σ] = T.|[σ >>> rename ξ].
Proof.
  elim: T ξ σ =>[^~s] ξ σ; rewrite /= ? up_comp_subst_ren_internal; f_equal;
    trivial using vl_rename_Lemma, vl_comp_rename_Lemma, path_rename_comp_Lemma.
Qed.

Lemma path_comp_Lemma (σ τ : var → vl) p : p.|[σ].|[τ] = p.|[σ >> τ].
Proof.
  elim: p => [^~s]; rewrite /= ? up_comp_internal; f_equal;
    trivial using vl_rename_comp_Lemma, vl_comp_rename_Lemma, vl_comp_Lemma.
Qed.

Lemma ty_comp_Lemma (σ τ : var → vl) T : T.|[σ].|[τ] = T.|[σ >> τ].
Proof.
  elim: T σ τ => [^~s] σ τ; rewrite /= ? up_comp_internal; f_equal;
    trivial using vl_rename_comp_Lemma, vl_comp_rename_Lemma, path_comp_Lemma.
Qed.

Instance hsubst_lemmas_ty : HSubstLemmas vl ty.
Proof. split; trivial using ty_ids_Lemma, ty_comp_Lemma. Qed.

Instance hsubst_lemmas_pth : HSubstLemmas vl path.
Proof. split; trivial using path_ids_Lemma, path_comp_Lemma. Qed.

Instance hsubst_lemmas_ctx : HSubstLemmas vl ctx := _.

Instance sort_path : Sort path := {}.
Instance sort_ty : Sort ty := {}.

(** Induction principles for closed terms. *)
Section path_ind_closed.
  Implicit Types (n : nat).
  Variable Ppt : path → nat → Prop.

  Variable step_pv : ∀ n v1,
      nclosed_vl v1 n → nclosed (pv v1) n →
      Ppt (pv v1) n.
  Variable step_psefl : ∀ n p1 l,
      nclosed p1 n →
      Ppt p1 n → Ppt (pself p1 l) n.

  Lemma nclosed_path_mut_ind n p : nclosed p n → Ppt p n.
  Proof. elim: p => [^~s] Hcl; eauto 3 with fv. Qed.
End path_ind_closed.

Section type_ind_closed.
  Implicit Types (n : nat).

  Variable Pty : ty   → nat → Prop.

  Variable step_TTop : ∀ n,
      nclosed TTop n →
      Pty TTop n.
  Variable step_TBot : ∀ n,
      nclosed TBot n →
      Pty TBot n.

  Variable step_TAnd : ∀ n T1 T2,
      nclosed T1 n → nclosed T2 n → nclosed (TAnd T1 T2) n →
      Pty T1 n → Pty T2 n → Pty (TAnd T1 T2) n.
  Variable step_TOr : ∀ n T1 T2,
      nclosed T1 n → nclosed T2 n → nclosed (TOr T1 T2) n →
      Pty T1 n → Pty T2 n → Pty (TOr T1 T2) n.
  Variable step_TLater : ∀ n T1,
      nclosed T1 n → nclosed (TLater T1) n →
      Pty T1 n → Pty (TLater T1) n.
  Variable step_TAll : ∀ n T1 T2,
      nclosed T1 n → nclosed T2 (S n) → nclosed (TAll T1 T2) n →
      Pty T1 n → Pty T2 (S n) → Pty (TAll T1 T2) n.
  Variable step_TMu : ∀ n T1,
      nclosed T1 (S n) → nclosed (TMu T1) n →
      Pty T1 (S n) → Pty (TMu T1) n.
  Variable step_TVMem : ∀ n l T1,
      nclosed T1 n → nclosed (TVMem l T1) n →
      Pty T1 n → Pty (TVMem l T1) n.
  Variable step_TTMem : ∀ n l T1 T2,
      nclosed T1 n → nclosed T2 n → nclosed (TTMem l T1 T2) n →
      Pty T1 n → Pty T2 n → Pty (TTMem l T1 T2) n.
  Variable step_TSel : ∀ n p1 l,
      nclosed p1 n → nclosed (TSel p1 l) n →
      Pty (TSel p1 l) n.
  Variable step_TNat : ∀ n,
      nclosed TNat n →
      Pty TNat n.

  Lemma nclosed_ty_mut_ind n T : nclosed T n → Pty T n.
  (* Proof. revert n; induction T; intros n Hcl; eauto 3 with fv. Qed. *)
  Proof.
    elim: T n => [^~s] n Hcl;
    let byEapply p := efeed p using (fun q => apply q) by (eauto 2; eauto 1 with fv)
    in
      try match goal with
      (* Warning: add other arities as needed. *)
      | Hstep : context [?P (?c _ _ _) _] |- ?P (?c ?a1 ?a2 ?a3) _ => byEapply (Hstep n a1 a2 a3)
      | Hstep : context [?P (?c _ _) _] |- ?P (?c ?a1 ?a2) _ => byEapply (Hstep n a1 a2)
      | Hstep : context [?P (?c _) _] |- ?P (?c ?a1) _ => byEapply (Hstep n a1)
      | Hstep : context [?P (?c) _] |- ?P (?c) _ => byEapply (Hstep n)
      end.
  Qed.
End type_ind_closed.
