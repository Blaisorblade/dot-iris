From D Require Import tactics.
From D.DSub Require Import syn synLemmas.

Implicit Types (T: ty) (v: vl) (e: tm) (Γ : ctx).
Set Implicit Arguments.

(*
  TODO: part of this code implements a variant of lemmas in synLemmas, but for arbitrary substitutions, not just the ones produced
  by to_subst. Reducing the overlap might be good.
 *)
Definition nclosed_sub n m s :=
  ∀ i, i < n → nclosed_vl (s i) m.
Definition nclosed_ren n m (r: var → var) := nclosed_sub n m (ren r).

Lemma compose_sub_closed s s1 s2 i j:
  nclosed_sub i j s → eq_n_s s1 s2 j → eq_n_s (s >> s1) (s >> s2) i.
Proof. move => /= Hs Heqs x Hxi. exact: Hs. Qed.

Lemma nclosed_vl_ids_0 i: i > 0 → nclosed_vl (ids 0) i.
Proof. move => Hi s1 s2 /= Heqs. by apply Heqs. Qed.

Lemma nclosed_vl_ids_S i j: nclosed_vl (ids i) j → nclosed_vl (ids (S i)) (S j).
Proof.
  move => /= Hij s1 s2 Heqs. apply: Heqs.
  suff: i < j by lia. by apply nclosed_var_lt.
Qed.

Lemma nclosed_vl_ids i j: i < j → nclosed_vl (ids i) j.
Proof. move => Hj s1 s2 Hseq /=. exact: Hseq. Qed.

Hint Resolve nclosed_vl_ids_0 nclosed_vl_ids_S nclosed_vl_ids.

Lemma nclosed_ren_shift n m j:
  m >= j + n → nclosed_ren n m (+j).
Proof. move=>???/=; eauto with lia. Qed.
Hint Resolve nclosed_ren_shift.

Lemma nclosed_sub_vl v s i j:
  nclosed_sub i j s →
  nclosed_vl v i → nclosed_vl v.[s] j.
Proof. move => Hcls Hclv s1 s2 Heqs; asimpl. by eapply Hclv, compose_sub_closed. Qed.

Lemma nclosed_sub_x `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A) s i j:
  nclosed_sub i j s →
  nclosed a i → nclosed a.|[s] j.
Proof. move => Hcls Hcla s1 s2 Heqs; asimpl. by eapply Hcla, compose_sub_closed. Qed.

Lemma nclosed_ren_vl v r i j:
  nclosed_ren i j r →
  nclosed_vl v i → nclosed_vl (rename r v) j.
Proof. asimpl; exact: nclosed_sub_vl. Qed.

Lemma nclosed_sub_up i j s:
  nclosed_sub i j s →
  nclosed_sub (S i) (S j) (up s).
Proof.
  move => //= Hs [|x] Hx. by eauto with lia.
  asimpl; rewrite -rename_subst.
  eapply nclosed_ren_vl; by eauto with lia.
Qed.
Hint Resolve nclosed_sub_up.

Lemma nclosed_ren_up n m r:
  nclosed_ren n m r →
  nclosed_ren (S n) (S m) (upren r).
Proof. move => //= Hr [|i] Hi; asimpl; eauto with lia. Qed.
Hint Resolve nclosed_ren_up.
