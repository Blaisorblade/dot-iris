From D Require Import tactics.
From D.DSub Require Import operational synLemmas.
From iris.program_logic Require Import ectx_lifting.

Set Implicit Arguments.
Implicit Types (T: ty) (v: vl) (t: tm).

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

  Theorem nclosed_head_step t1 t2 σ σ' ts n:
    head_step t1 σ [] t2 σ' ts →
    nclosed t1 n →
    nclosed t2 n.
  Proof.
    move => Hst Hcl; destruct Hst as [t1 v2|t]; [ exact (nclosed_beta Hcl) | solve_inv_fv_congruence_h Hcl ].
  Qed.
  Hint Resolve nclosed_head_step.

  Inductive nclosed_ectx_item: ectx_item → nat → Prop :=
  | ClAppLCtx t2 n: nclosed t2 n → nclosed_ectx_item (AppLCtx t2) n
  | ClAppRCtx v1 n: nclosed_vl v1 n → nclosed_ectx_item (AppRCtx v1) n.
  Hint Constructors nclosed_ectx_item.

  Notation nclosed_ectx K n := (Forall (λ Ki, nclosed_ectx_item Ki n) K).

  Lemma nclosed_fill_item_inv_t Ki t n: nclosed (fill_item Ki t) n → nclosed t n.
  Proof. case: Ki => [e2|v1] /=; solve_inv_fv_congruence. Qed.
  Hint Resolve nclosed_fill_item_inv_t.

  Lemma nclosed_fill_item_inv_Ki Ki t n: nclosed (fill_item Ki t) n → nclosed_ectx_item Ki n.
  Proof. case: Ki => [e2|v1] Hcl /=; constructor; solve_inv_fv_congruence_h Hcl. Qed.
  Hint Resolve nclosed_fill_item_inv_Ki.

  Lemma nclosed_fill_inv_t K t n: nclosed (fill K t) n → nclosed t n.
  Proof. elim: K t => //= Ki K IHK t Hcl; eauto. Qed.
  Hint Resolve nclosed_fill_inv_t.

  Lemma nclosed_fill_inv_K K t n: nclosed (fill K t) n → nclosed_ectx K n.
  Proof. elim: K t => //= Ki K IHK t Hcl; eauto. Qed.
  Hint Resolve nclosed_fill_inv_K.

  Lemma nclosed_fill_item Ki t n: nclosed t n → nclosed_ectx_item Ki n → nclosed (fill_item Ki t) n.
  Proof.
    case: Ki => [e2|v1] /= Hclt HclKi; inverse HclKi; solve_fv_congruence.
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
