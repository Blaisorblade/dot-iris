From D Require Import tactics.
From D.Dot Require Import syn synLemmas.
From iris.program_logic Require Import ectx_language.

Set Implicit Arguments.
Implicit Types (T: ty) (v: vl) (t: tm) (d: dm) (ds: dms).

Section nclosed_prim_step.
  Lemma nclosed_beta t1 v2 n:
    nclosed (tapp (tv (vabs t1)) (tv v2)) n →
    nclosed t1.|[v2/] n.
  Proof. move => Hcl. apply nclosed_subst; eauto with fv. Qed.

  Lemma nclosed_path2tm p n :
    nclosed p n →
    nclosed (path2tm p) n.
  Proof.
    elim: p => [v|p IHp l] /=;
      eauto using fv_of_val, fv_pv_inv, fv_pself_inv, fv_tproj.
  Qed.

  Lemma nclosed_proj v l p n:
    v @ l ↘ dvl p →
    nclosed (tproj (tv v) l) n →
    nclosed (path2tm p) n.
  Proof.
    move => Hl Hcl.
    apply nclosed_path2tm.
    enough (nclosed (dvl p) n) by eauto with fv.
    apply (nclosed_lookup' Hl). eauto with fv.
  Qed.

  Lemma nclosed_un_op_eval u v w n :
    un_op_eval u v = Some w →
    nclosed (tun u (tv v)) n →
    nclosed (tv w) n.
  Proof.
    rewrite /un_op_eval => Hev Hcl; apply fv_of_val.
    assert (Hclt1: nclosed_vl v n) by eauto with fv.
    by repeat (case_match; simplify_eq).
  Qed.

  Lemma nclosed_bin_op_eval b v1 v2 w n :
    bin_op_eval b v1 v2 = Some w →
    nclosed (tbin b (tv v1) (tv v2)) n →
    nclosed (tv w) n.
  Proof.
    move => Hev Hcl; apply fv_of_val.
    assert (Hclt1: nclosed_vl v1 n) by eauto with fv.
    assert (Hclt2: nclosed_vl v2 n) by eauto with fv.
    unfold bin_op_eval, bin_op_eval_nat, bin_op_eval_bool in *.
    by repeat (case_match; simplify_eq).
  Qed.

  Theorem nclosed_head_step t1 t2 σ σ' ts κ n:
    head_step t1 σ κ t2 σ' ts →
    nclosed t1 n →
    nclosed t2 n.
  Proof.
    move => Hst Hcl; destruct Hst; by [
      exact (nclosed_beta Hcl) | eapply nclosed_proj |
      eapply nclosed_un_op_eval | eapply nclosed_bin_op_eval |
      solve_inv_fv_congruence_h Hcl ].
  Qed.

  Theorem nclosed_head_step_efs t1 t2 σ σ' ts κ n:
    head_step t1 σ κ t2 σ' ts →
    nclosed t1 n →
    Forall (flip nclosed n) ts.
  Proof. move => Hst Hcl; by destruct Hst. Qed.

  Hint Resolve nclosed_head_step nclosed_head_step_efs : core.

  Inductive nclosed_ectx_item: ectx_item → nat → Prop :=
  | ClAppLCtx t2 n: nclosed t2 n → nclosed_ectx_item (AppLCtx t2) n
  | ClAppRCtx v1 n: nclosed_vl v1 n → nclosed_ectx_item (AppRCtx v1) n
  | ClProjCtx l n: nclosed_ectx_item (ProjCtx l) n
  | ClSkipCtx n: nclosed_ectx_item SkipCtx n
  | ClUnCtx u n : nclosed_ectx_item (UnCtx u) n
  | ClBinLCtx b t2 n: nclosed t2 n → nclosed_ectx_item (BinLCtx b t2) n
  | ClBinRCtx b v1 n: nclosed_vl v1 n → nclosed_ectx_item (BinRCtx b v1) n
  | ClIfCtx t1 t2 n : nclosed t1 n → nclosed t2 n → nclosed_ectx_item (IfCtx t1 t2) n.
  Hint Constructors nclosed_ectx_item : core.

  Notation nclosed_ectx K n := (Forall (λ Ki, nclosed_ectx_item Ki n) K).

  Lemma nclosed_fill_item_inv_t Ki t n: nclosed (fill_item Ki t) n → nclosed t n.
  Proof. destruct Ki => /=; solve_inv_fv_congruence. Qed.
  Hint Resolve nclosed_fill_item_inv_t : core.

  Lemma nclosed_fill_item_inv_Ki Ki t n: nclosed (fill_item Ki t) n → nclosed_ectx_item Ki n.
  Proof. destruct Ki => Hcl /=; constructor; solve_inv_fv_congruence_h Hcl. Qed.
  Hint Resolve nclosed_fill_item_inv_Ki : core.

  Lemma nclosed_fill_inv_t K t n: nclosed (fill K t) n → nclosed t n.
  Proof. elim: K t => //= Ki K IHK t Hcl; eauto. Qed.
  Hint Resolve nclosed_fill_inv_t : core.

  Lemma nclosed_fill_inv_K K t n: nclosed (fill K t) n → nclosed_ectx K n.
  Proof. elim: K t => //= Ki K IHK t Hcl; eauto. Qed.
  Hint Resolve nclosed_fill_inv_K : core.

  Lemma nclosed_fill_item Ki t n: nclosed t n → nclosed_ectx_item Ki n → nclosed (fill_item Ki t) n.
  Proof. destruct Ki => /= Hclt HclKi; inverse HclKi; solve_fv_congruence. Qed.
  Hint Resolve nclosed_fill_item : core.

  Lemma nclosed_fill K t n: nclosed t n → nclosed_ectx K n → nclosed (fill K t) n.
  Proof. elim: K t => //= Ki K IHK t Hclt HclKKi; inverse HclKKi; eauto. Qed.
  Hint Resolve nclosed_fill : core.

  Lemma nclosed_fill_inv K t n: nclosed (fill K t) n → nclosed t n ∧ nclosed_ectx K n.
  Proof. split; eauto. Qed.

  Theorem nclosed_prim_step t1 t2 σ σ' ts κ n:
    prim_step t1 σ κ t2 σ' ts →
    nclosed t1 n →
    nclosed t2 n ∧ Forall (flip nclosed n) ts.
  Proof. move => [K t1' t2' -> -> Hhst] /nclosed_fill_inv [??]; eauto. Qed.
End nclosed_prim_step.
