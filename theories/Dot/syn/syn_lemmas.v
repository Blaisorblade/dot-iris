(** * Free-variable lemmas for DOT.
To limit compile times, do not load this file in unary_lr. *)
From D.Dot Require Import syn.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms)
         (Γ : ctx) (ρ : vls).

(** Here is a manual proof of [fv_vabs_inv], with explanations. *)
Lemma fv_vabs_inv_manual e n : nclosed_vl (vabs e) n → nclosed e (S n).
Proof.
  rewrite /nclosed_vl /nclosed => /= Hfv s1 s2 HsEq.

  (* From [Hfv], we only learn that [e.|[up s1] = e.|[up s2]], for arbitrary
  [s1] and [s2], but substitutions in our thesis [e.|[s1] = e.|[s2]] are not
  of form [up ?]. Hence, we rewrite it using [decomp_s] / [decomp_s_vl] to
  get a substitution of form [up ?], then rewrite with [e.|[up (stail s1)] =
  e.|[up (stail s2)]] (got from [Hfv]), and conclude.
      *)
  rewrite ?(decomp_s _ s1) ?(decomp_s _ s2) ?(decomp_s_vl _ s1) ?(decomp_s_vl _ s2) (eq_n_s_heads HsEq); last lia.
  injection (Hfv _ _ (eq_n_s_tails HsEq)); rewritePremises; reflexivity.
Qed.

(** The following ones are "direct" lemmas: deduce that an expression is closed
    by knowing that its subexpression are closed. *)

Lemma fv_vobj ds n: nclosed ds (S n) → nclosed_vl (vobj ds) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_vabs_inv e n: nclosed_vl (vabs e) n → nclosed e (S n).
Proof. solve_inv_fv_congruence. Qed.
