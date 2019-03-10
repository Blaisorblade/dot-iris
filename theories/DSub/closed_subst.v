From D Require Import tactics.
From D.DSub Require Import syn synLemmas.

Implicit Types (T: ty) (v: vl) (e: tm) (Γ : ctx).
Set Implicit Arguments.

Definition nclosed_sub n m s :=
  ∀ i, i < n → nclosed_vl (s i) m.
Definition nclosed_ren n m (r: var → var) := nclosed_sub n m (ren r).

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

Lemma nclosed_ren_up n m r:
  nclosed_ren n m r →
  nclosed_ren (S n) (S m) (upren r).
Proof. move => //= Hr [|i] Hi; asimpl; eauto with lia. Qed.
Hint Resolve nclosed_ren_up.

Lemma nclosed_ren_mut:
  (∀ e i,
    nclosed e i →
    ∀ r j, nclosed_ren i j r →
    nclosed (rename r e) j) ∧
  (∀ v i,
    nclosed_vl v i →
    ∀ r j, nclosed_ren i j r →
    nclosed_vl (rename r v) j) ∧
  (∀ T i,
    nclosed T i →
    ∀ r j, nclosed_ren i j r →
    nclosed (rename r T) j).
Proof.
  apply nclosed_syntax_mut_ind => n.
  all: try by [intros; move => /= s1 s2 Heqs; f_equal; naive_solver eauto using eq_up].
  (* - move => v Hclv ? IHv. r j Hr s1 s2 Heqs /=; f_equal; asimpl.
    eapply IHv => /= *. eauto. eauto using eq_up. apply Hr. *)
  - move => t Ht _ IHt r j Hr s1 s2 Heqs /=; f_equal; eapply IHt; eauto using eq_up.
  - intros; eapply fv_vstamp; rewrite //= ?Forall_fmap; decompose_Forall; eauto.
  - move => T1 T2 HT1 HT2 _ IHT1 IHT2 r j Hr s1 s2 Heqs /=; f_equal; first naive_solver.
    eapply IHT2; eauto using eq_up.
Qed.

Lemma nclosed_ren_vl: ∀ v r i j,
    nclosed_ren i j r →
    nclosed_vl v i →
    nclosed_vl (rename r v) j.
Proof. unmut_lemma nclosed_ren_mut. Qed.

Lemma nclosed_ren_shift n m j:
  m >= j + n → nclosed_ren n m (+j).
Proof. move=>???/=; eauto with lia. Qed.
Hint Resolve nclosed_ren_shift.

Lemma nclosed_sub_up i j s:
  nclosed_sub i j s →
  nclosed_sub (S i) (S j) (up s).
Proof.
  move => //= Hs [|x] Hx. by eauto with lia.
  asimpl; rewrite -rename_subst.
  eapply nclosed_ren_vl; by eauto with lia.
Qed.
Hint Resolve nclosed_sub_up.

Lemma nclosed_sub_mut:
  (∀ e i,
    nclosed e i →
    ∀ s j, nclosed_sub i j s →
    nclosed e.|[s] j) ∧
  (∀ v i,
    nclosed_vl v i →
    ∀ s j, nclosed_sub i j s →
    nclosed_vl v.[s] j) ∧
  (∀ T i,
    nclosed T i →
    ∀ s j, nclosed_sub i j s →
    nclosed T.|[s] j).
Proof.
  apply nclosed_syntax_mut_ind => n.
  all: try by [intros; move => /= s1 s2 Heqs; f_equal; naive_solver eauto using eq_up].
  - move => v Hv s j Hs s1 s2 Heqs /=.
    eapply Hs; eauto.
  - move => t Ht _ IHt s j Hs s1 s2 Heqs /=; f_equal. eapply IHt; eauto using eq_up.
  - intros; eapply fv_vstamp; rewrite //= ?Forall_fmap; decompose_Forall; eauto.
  - move => T1 T2 HT1 HT2 _ IHT1 IHT2 s j Hs s1 s2 Heqs /=; f_equal; first naive_solver.
    eapply IHT2; eauto using eq_up.
Qed.

Lemma nclosed_sub_vl: ∀ v s i j,
  nclosed_sub i j s →
  nclosed_vl v i →
  nclosed_vl v.[s] j.
Proof. unmut_lemma nclosed_sub_mut. Qed.
