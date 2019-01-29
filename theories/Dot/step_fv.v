From D Require Import tactics.
From D.Dot Require Import operational synLemmas.
From iris.program_logic Require Import ectx_lifting.

Set Implicit Arguments.
Implicit Types (T: ty) (v: vl) (t: tm) (d: dm) (ds: dms).

Section nclosed_prim_step.
  Lemma nclosed_subst `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A) v n:
    nclosed a (S n) →
    nclosed_vl v n →
    nclosed a.|[v/] n.
  Proof.
    move => Hclt1 Hclv.
    move => s1 s2 HsEq /=; asimpl.
    apply Hclt1.
    move => [|x] Hxn //=; auto with lia.
  Qed.

  Lemma nclosed_beta t1 v2 n:
    nclosed (tapp (tv (vabs t1)) (tv v2)) n →
    nclosed t1.|[v2/] n.
  Proof. move => Hcl. apply nclosed_subst; eauto with fv. Qed.

  Lemma nclosed_selfSubst ds n:
    nclosed ds (S n) → nclosed (selfSubst ds) n.
  Proof. move => Hcl. by apply nclosed_subst, fv_vobj. Qed.

  Lemma fv_head d ds n: nclosed (d :: ds) n → nclosed d n.
  Proof. solve_inv_fv_congruence. Qed.
  Hint Resolve fv_head: fvl.

  Lemma fv_tail d ds n: nclosed (d :: ds) n → nclosed ds n.
  Proof. solve_inv_fv_congruence. Qed.
  Hint Resolve fv_tail: fvl.
  Hint Resolve fv_dms_cons: fvl.

  Lemma nclosed_rev_append (ds1 ds2: dms) n: nclosed ds1 n → nclosed ds2 n → nclosed (rev_append ds1 ds2) n.
  Proof.
    elim: ds1 ds2 => [|d1 ds1 IHds1] //= ds2 Hcl1 Hcl2.
    assert (Hcld1: nclosed d1 n) by eauto with fvl.
    assert (Hclds1: nclosed ds1 n) by eauto with fvl.
    by apply IHds1, fv_dms_cons.
  Qed.

  Lemma nclosed_reverse ds n: nclosed ds n → nclosed (reverse ds) n.
  Proof. move => Hcl. by apply nclosed_rev_append. Qed.

  Lemma nclosed_lookup ds d n l: nclosed ds n → ds !! l = Some d → nclosed d n.
  Proof. elim: ds l => [|d' ds IHds] [|l] //= Hcl Heq; simplify_eq; eauto with fvl. Qed.

  Lemma nclosed_proj ds l v n:
    reverse (selfSubst ds) !! l = Some (dvl v) →
    nclosed (tproj (tv (vobj ds)) l) n →
    nclosed (tv v) n.
  Proof.
    move => Hl Hcl.
    assert (Hclt1: nclosed ds (S n)) by eauto with fv.
    apply fv_tv.
    enough (nclosed (dvl v) n) by eauto with fv.
    eapply nclosed_lookup => //. by eapply nclosed_reverse, nclosed_selfSubst.
  Qed.

  Theorem nclosed_head_step t1 t2 σ σ' ts n:
    head_step t1 σ [] t2 σ' ts →
    nclosed t1 n →
    nclosed t2 n.
  Proof.
    move => Hst Hcl; destruct Hst as [t1 v2| |t]; by [> exact (nclosed_beta Hcl) | eapply nclosed_proj | solve_inv_fv_congruence_h Hcl ].
  Qed.
  Hint Resolve nclosed_head_step.

  Inductive nclosed_ectx_item: ectx_item → nat → Prop :=
  | ClAppLCtx t2 n: nclosed t2 n → nclosed_ectx_item (AppLCtx t2) n
  | ClAppRCtx v1 n: nclosed_vl v1 n → nclosed_ectx_item (AppRCtx v1) n
  | ClProjCtx l n: nclosed_ectx_item (ProjCtx l) n.
  Hint Constructors nclosed_ectx_item.

  Notation nclosed_ectx K n := (Forall (λ Ki, nclosed_ectx_item Ki n) K).

  Lemma nclosed_fill_item_inv_t Ki t n: nclosed (fill_item Ki t) n → nclosed t n.
  Proof. case: Ki => [e2|v1|l] /=; solve_inv_fv_congruence. Qed.
  Hint Resolve nclosed_fill_item_inv_t.

  Lemma nclosed_fill_item_inv_Ki Ki t n: nclosed (fill_item Ki t) n → nclosed_ectx_item Ki n.
  Proof. case: Ki => [e2|v1|l] Hcl /=; constructor; solve_inv_fv_congruence_h Hcl. Qed.
  Hint Resolve nclosed_fill_item_inv_Ki.

  Lemma nclosed_fill_inv_t K t n: nclosed (fill K t) n → nclosed t n.
  Proof. elim: K t => //= Ki K IHK t Hcl; eauto. Qed.
  Hint Resolve nclosed_fill_inv_t.

  Lemma nclosed_fill_inv_K K t n: nclosed (fill K t) n → nclosed_ectx K n.
  Proof. elim: K t => //= Ki K IHK t Hcl; eauto. Qed.
  Hint Resolve nclosed_fill_inv_K.

  Lemma nclosed_fill_item Ki t n: nclosed t n → nclosed_ectx_item Ki n → nclosed (fill_item Ki t) n.
  Proof.
    case: Ki => [e2|v1|l] /= Hclt HclKi; inverse HclKi; solve_fv_congruence.
  Qed.
  Hint Resolve nclosed_fill_item.

  Lemma nclosed_fill K t n: nclosed t n → nclosed_ectx K n → nclosed (fill K t) n.
  Proof. elim: K t => //= Ki K IHK t Hclt HclKKi; inverse HclKKi; eauto. Qed.
  Hint Resolve nclosed_fill.

  Theorem nclosed_prim_step t1 t2 σ σ' ts n:
    nclosed t1 n →
    prim_step t1 σ [] t2 σ' ts →
    nclosed t2 n.
  Proof.
    move => Hclt1 [K t1' t2' Heqe1 Heqe2 Hhst] /=; subst; cbn in *.
    eapply nclosed_fill; eauto.
  Qed.
End nclosed_prim_step.
