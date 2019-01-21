From D Require Import tactics.
From D.DSub Require Import operational synLemmas.
From iris.program_logic Require Import ectx_lifting.

Set Implicit Arguments.
Implicit Types (T: ty) (v: vl) (t: tm).

Section nclosed_prim_step.
  Lemma nclosed_beta t1 v2 n:
    nclosed (tapp (tv (vabs t1)) (tv v2)) n →
    nclosed t1.|[v2/] n.
  Proof.
    move => Hcl.
    assert (Hclt1: nclosed t1 (S n)) by solve_inv_fv_congruence_h Hcl.
    assert (Hclv2: nclosed_vl v2 n) by solve_inv_fv_congruence_h Hcl.
    move => s1 s2 HsEq /=; asimpl.
    apply Hclt1.
    move => [|x] Hxn //=; auto with lia.
  Qed.

  Theorem nclosed_head_step t1 t2 σ σ' ts n:
    nclosed t1 n →
    head_step t1 σ [] t2 σ' ts →
    nclosed t2 n.
  Proof.
    move => Hcl Hst; destruct Hst as [t1 v2|t]; [ exact (nclosed_beta Hcl) | solve_inv_fv_congruence_h Hcl ].
  Qed.

  Inductive nclosed_ectx_item: ectx_item → nat → Prop :=
  | ClAppLCtx t2 n: nclosed t2 n → nclosed_ectx_item (AppLCtx t2) n
  | ClAppRCtx v1 n: nclosed_vl v1 n → nclosed_ectx_item (AppRCtx v1) n.
  Hint Constructors nclosed_ectx_item.

  Notation nclosed_ectx K n := (Forall (λ Ki, nclosed_ectx_item Ki n) K).

  Lemma nclosed_fill_item_inv_t Ki t n: nclosed (fill_item Ki t) n → nclosed t n.
  Proof. case: Ki => [e2|v1] /=; solve_inv_fv_congruence. Qed.

  Lemma nclosed_fill_item_inv_Ki Ki t n: nclosed (fill_item Ki t) n → nclosed_ectx_item Ki n.
  Proof. case: Ki => [e2|v1] Hcl /=; constructor; solve_inv_fv_congruence_h Hcl. Qed.

  Lemma nclosed_fill_inv_t K t n: nclosed (fill K t) n → nclosed t n.
  Proof. elim: K t => //= Ki K IHK t Hcl. by apply (nclosed_fill_item_inv_t Ki), IHK, Hcl. Qed.

  Lemma nclosed_fill_inv_K K t n: nclosed (fill K t) n → nclosed_ectx K n.
  Proof.
    elim: K t => //= Ki K IHK t Hcl.
    eauto using nclosed_fill_item_inv_Ki, nclosed_fill_inv_t.
  Qed.

  Lemma nclosed_fill_item Ki t n: nclosed t n → nclosed_ectx_item Ki n → nclosed (fill_item Ki t) n.
  Proof.
    case: Ki => [e2|v1] /= Hclt HclKi; inverse HclKi; try solve_fv_congruence.
    eauto using fv_tv, fv_tapp.
  Qed.

  Lemma nclosed_fill K t n: nclosed t n → nclosed_ectx K n → nclosed (fill K t) n.
  Proof.
    elim: K t => //= Ki K IHK t Hclt HclKKi. inverse HclKKi.
    apply IHK => //. by apply nclosed_fill_item.
  Qed.

  Theorem nclosed_prim_step t1 t2 σ σ' ts n:
    nclosed t1 n →
    prim_step t1 σ [] t2 σ' ts →
    nclosed t2 n.
  Proof.
    move => Hclt1 [K t1' t2' Heqe1 Heqe2 Hhst] /=; subst; cbn in *.
    eapply nclosed_fill, nclosed_fill_inv_K => //.
    eapply nclosed_head_step, Hhst. by eapply nclosed_fill_inv_t.
  Qed.
End nclosed_prim_step.
