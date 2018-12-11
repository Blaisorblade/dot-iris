(**
Lemmas on SynFuncs.v needed for proofs on the operational semantics.
To reduce compile times, unary_lr should not depend on this file.
This file should load as little Iris code as possible, to reduce compile times. But we must import operational.
 *)
Require Import Dot.tactics.
Require Export Dot.dotsyn.
Require Export Dot.operational.

(** Rewrite v ↗ ds to vobj ds' ↗ ds. *)
Ltac simplOpen ds' :=
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

Lemma length_idsσr n r: length (idsσ n).|[ren r] = n.
Proof.
  elim : n r => [r | n IHn r] => //.
  asimpl. by rewrite IHn.
Qed.

Lemma length_idsσ n: length (idsσ n) = n.
Proof. pose proof (length_idsσr n (+0)) as Hr. asimpl in Hr. exact Hr. Qed.

Lemma subst_sigma_idsσ ρ n : length ρ = n →
                (subst_sigma (idsσ n) ρ) ≡ ρ.
Proof.
  rewrite /subst_sigma. move :n.
  induction ρ => *; subst => //; asimpl.
  f_equal. by apply IHρ.
Qed.
