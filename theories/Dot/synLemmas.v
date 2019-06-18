(**
To reduce compile times, unary_lr should not depend on this file.
This file should load as little Iris code as possible, to reduce compile times.
 *)
From D Require Import tactics.
From D.Dot Require Import syn.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms)
         (Γ : ctx) (ρ : vls).

(** The following ones are "direct" lemmas: deduce that an expression is closed
    by knowing that its subexpression are closed. *)

Lemma fv_tskip e n: nclosed e n → nclosed (tskip e) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_tproj e l n: nclosed e n → nclosed (tproj e l) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_tapp e1 e2 n: nclosed e1 n → nclosed e2 n → nclosed (tapp e1 e2) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_tv v n: nclosed_vl v n → nclosed (tv v) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_vobj ds n: nclosed ds (S n) → nclosed_vl (vobj ds) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_vabs e n: nclosed e (S n) → nclosed_vl (vabs e) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_dvl v n: nclosed_vl v n → nclosed (dvl v) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_dtysyn T n: nclosed T n → nclosed (dtysyn T) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_pv v n: nclosed_vl v n → nclosed (pv v) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_pself p l n: nclosed p n → nclosed (pself p l) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_TAnd T1 T2 n: nclosed T1 n →
                       nclosed T2 n →
                       nclosed (TAnd T1 T2) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_TOr T1 T2 n: nclosed T1 n →
                       nclosed T2 n →
                       nclosed (TOr T1 T2) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_TMu T1 n: nclosed T1 (S n) → nclosed (TMu T1) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_TLater T n: nclosed T n → nclosed (TLater T) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_TAll T1 T2 n: nclosed T1 n →
                       nclosed T2 (S n) →
                       nclosed (TAll T1 T2) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_TVMem l T1 n: nclosed T1 n →
                       nclosed (TVMem l T1) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_TTMem l T1 T2 n: nclosed T1 n →
                        nclosed T2 n →
                        nclosed (TTMem l T1 T2) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_TSel p l n: nclosed p n → nclosed (TSel p l) n.
Proof. solve_fv_congruence. Qed.

Definition fv_dms_cons : ∀ l d ds n, nclosed ds n → nclosed d n → nclosed ((l, d) :: ds) n := fv_pair_cons.

Lemma fv_dtysem σ s n: nclosed_σ σ n → nclosed (dtysem σ s) n.
Proof. move => /Forall_to_closed_vls. solve_fv_congruence. Qed.

Lemma fv_dtysem_inv σ s n: nclosed (dtysem σ s) n → nclosed_σ σ n.
Proof. intro. apply closed_vls_to_Forall. eauto with fv. Qed.




Lemma fv_tv_inv v n: nclosed (tv v) n → nclosed_vl v n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_tapp_inv_1 n e1 e2: nclosed (tapp e1 e2) n → nclosed e1 n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_tapp_inv_2 n e1 e2: nclosed (tapp e1 e2) n → nclosed e2 n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_tskip_inv t n: nclosed (tskip t) n → nclosed t n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_vabs_inv e n: nclosed_vl (vabs e) n → nclosed e (S n).
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_vobj_inv ds n: nclosed_vl (vobj ds) n → nclosed ds (S n).
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_pv_inv v n: nclosed (pv v) n → nclosed_vl v n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_TMu_inv T1 n: nclosed (TMu T1) n → nclosed T1 (S n).
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_TAll_inv_1 n T1 T2: nclosed (TAll T1 T2) n → nclosed T1 n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_TAll_inv_2 n T1 T2: nclosed (TAll T1 T2) n → nclosed T2 (S n).
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_TTMem_inv_1 n l T1 T2: nclosed (TTMem l T1 T2) n → nclosed T1 n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_TTMem_inv_2 n l T1 T2: nclosed (TTMem l T1 T2) n → nclosed T2 n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_TSel_inv p l n: nclosed (TSel p l) n → nclosed p n.
Proof. solve_inv_fv_congruence. Qed.

Lemma nclosed_tskip_i e n i:
  nclosed e n →
  nclosed (iterate tskip i e) n.
Proof.
  move => Hcl; elim: i => [|i IHi]; rewrite ?iterate_0 ?iterate_S //; solve_fv_congruence.
Qed.

Lemma tskip_subst i e s: (iterate tskip i e).|[s] = iterate tskip i e.|[s].
Proof. elim: i => [|i IHi]; by rewrite ?iterate_0 ?iterate_S //= IHi. Qed.

Lemma lookup_fv Γ x T: Γ !! x = Some T → nclosed (tv (ids x)) (length Γ).
Proof. move =>/lookup_ids_fv /fv_tv //. Qed.

Lemma fv_head l d ds n: nclosed ((l, d) :: ds) n → nclosed d n.
Proof. exact: fv_cons_pair_inv_head. Qed.

Lemma fv_tail l d ds n: nclosed ((l, d) :: ds) n → nclosed ds n.
Proof. exact: fv_cons_pair_inv_tail. Qed.

Lemma nclosed_selfSubst ds n:
  nclosed ds (S n) → nclosed (selfSubst ds) n.
Proof. move => ?. by apply /nclosed_subst /fv_vobj. Qed.

Lemma nclosed_lookup ds d n l: dms_lookup l ds = Some d → nclosed ds n → nclosed d n.
Proof.
  elim: ds => [|[l' d'] ds IHds] //= Heq Hcl.
  case_decide; simplify_eq; eauto using fv_head, fv_tail.
Qed.

Lemma nclosed_lookup' {w l d n}: w @ l ↘ d → nclosed_vl w n → nclosed d n.
Proof. move => [ds [->]] Hl /fv_vobj_inv /nclosed_selfSubst. exact: nclosed_lookup. Qed.

Lemma plength_subst_inv p s :
  plength p.|[s] = plength p.
Proof. by elim: p => [v| p /= ->]. Qed.
