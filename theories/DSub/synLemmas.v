(**
Lemmas on SynFuncs.v needed for proofs on the operational semantics.
To reduce compile times, unary_lr should not depend on this file.
This file should load as little Iris code as possible, to reduce compile times.
 *)
From D Require Import tactics.
From D.DSub Require Import syn.

Implicit Types
         (L T U: ty) (v: vl) (e: tm)
         (Γ : ctx) (ρ : vls).

(** The following ones are "direct" lemmas: deduce that an expression is closed
    by knowing that its subexpression are closed. *)

Lemma fv_tskip e n: nclosed e n → nclosed (tskip e) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_tapp e1 e2 n: nclosed e1 n → nclosed e2 n → nclosed (tapp e1 e2) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_tv v n: nclosed_vl v n → nclosed (tv v) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_vabs e n: nclosed e (S n) → nclosed_vl (vabs e) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_vty T n: nclosed T n → nclosed_vl (vty T) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_TLater T n: nclosed T n → nclosed (TLater T) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_TAll T1 T2 n: nclosed T1 n →
                       nclosed T2 (S n) →
                       nclosed (TAll T1 T2) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_TTMem T1 T2 n: nclosed T1 n →
                        nclosed T2 n →
                        nclosed (TTMem T1 T2) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_TSel v n: nclosed_vl v n → nclosed (TSel v) n.
Proof. solve_fv_congruence. Qed.



Lemma fv_vstamp σ s n: nclosed_σ σ n → nclosed_vl (vstamp σ s) n.
Proof. move => /Forall_to_closed_vls. solve_fv_congruence. Qed.

Lemma fv_vstamp_inv σ s n: nclosed_vl (vstamp σ s) n → nclosed_σ σ n.
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

Lemma fv_TAll_inv_1 n T1 T2: nclosed (TAll T1 T2) n → nclosed T1 n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_TAll_inv_2 n T1 T2: nclosed (TAll T1 T2) n → nclosed T2 (S n).
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_TTMem_inv_1 n T1 T2: nclosed (TTMem T1 T2) n → nclosed T1 n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_TTMem_inv_2 n T1 T2: nclosed (TTMem T1 T2) n → nclosed T2 n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_TSel_inv v n: nclosed (TSel v) n → nclosed_vl v n.
Proof. solve_inv_fv_congruence. Qed.

Lemma nclosed_tskip_i e n i:
  nclosed e n →
  nclosed (iterate tskip i e) n.
Proof.
  move => Hcl; elim: i => [|i IHi]; rewrite ?iterate_0 ?iterate_S //; solve_fv_congruence.
Qed.

Lemma tskip_subst i e s: (iterate tskip i e).|[s] = iterate tskip i e.|[s].
Proof. elim: i => [|i IHi]; by rewrite ?iterate_0 ?iterate_S //= IHi. Qed.
