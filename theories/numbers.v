From D Require Import prelude succ_notation.

(* Nat.succ_lt_mono is awkward as a view. *)
Lemma Nat_succ_lt_mono_rev {n m} : n.+1 < m.+1 ↔ n < m.
Proof. by rewrite -Nat.succ_lt_mono. Qed.
Lemma Nat_add_succ_r_l n m : n.+1 + m = n + m.+1.
Proof. by rewrite Nat.add_comm Nat.add_succ_r -Nat.add_succ_l Nat.add_comm. Qed.
