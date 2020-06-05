(**
Binding lemmas about D<:.
To reduce compile times, unary_lr should not depend on this file.
This file should load as little Iris code as possible, to reduce compile times.
 *)
From D.DSub Require Import ds_syn.

Implicit Types
         (L T U: ty) (v: vl) (e: tm)
         (Γ : ctx) (ρ : vls).

(** The following ones are "direct" lemmas: deduce that an expression is closed
    by knowing that its subexpression are closed. *)

Lemma tskip_subst i e s: (iterate tskip i e).|[s] = iterate tskip i e.|[s].
Proof. elim: i => [|i IHi]; by rewrite ?iterate_0 ?iterate_S //= IHi. Qed.



Lemma fv_vabs_inv e n: nclosed_vl (vabs e) n → nclosed e (S n).
Proof. solve_inv_fv_congruence. Qed.
