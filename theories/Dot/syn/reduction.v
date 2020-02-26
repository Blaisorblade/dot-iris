From iris.program_logic Require Import language ectx_language ectxi_language.
From D Require Import prelude.
From D.Dot Require Import syn.

Set Implicit Arguments.
Local Hint Constructors rtc nsteps : core.

Module Import relations.
Section R.
  Context `(R : relation A).
  Definition reducible a1 := ∃ a2, R a1 a2.
  Definition diverges a1 :=
    ∀ a2, rtc R a1 a2 → reducible a2.

  Lemma diverges_nsteps a1 n : diverges a1 → ∃ a2, nsteps R n a1 a2.
  Proof.
    move=> Hdiv.
    elim: n => [|n [a2 Hreds]]; first by exists a1; auto.
    have [a3 Hred]: reducible a2 by eapply Hdiv, nsteps_rtc, Hreds.
    exists a3. exact: nsteps_r.
  Qed.
  End R.
End relations.

Implicit Types
         (v : vl) (e t : tm) (d : dm) (ds : dms) (p : path)
         (vs : vls) (l : label).
Implicit Types (K : ectx_item) (Ks : list ectx_item).

Module simpl_red.
  Inductive ctx_closure (R : relation tm) : relation tm :=
    Ectx_step Ks t1 t2 :
      R t1 t2 → ctx_closure R (fill Ks t1) (fill Ks t2).
  Global Hint Constructors ctx_closure : core.

  Lemma Ectx_step' (R : relation tm) Ks t1 t2 t1' t2' :
    R t1 t2 → t1' = fill Ks t1 → t2' = fill Ks t2 →
    ctx_closure R t1' t2'.
  Proof. naive_solver. Qed.

  Inductive erased_head_step : tm -> tm -> Prop :=
  | est_beta t1 v2:
    erased_head_step (tapp (tv (vabs t1)) (tv v2)) (t1.|[v2/])
  | est_proj v l p:
    v @ l ↘ dpt p →
    erased_head_step (tproj (tv v) l) (path2tm p)
  | est_un u v1 v:
    un_op_eval u v1 = Some v →
    erased_head_step (tun u (tv v1)) (tv v)
  | est_bin b v1 v2 v:
    bin_op_eval b v1 v2 = Some v →
    erased_head_step (tbin b (tv v1) (tv v2)) (tv v)
  | est_iftrue e1 e2:
    erased_head_step (tif (tv $ vlit $ lbool true) e1 e2) e1
  | est_iffalse e1 e2:
    erased_head_step (tif (tv $ vlit $ lbool false) e1 e2) e2.
  Notation erased_step := (ctx_closure erased_head_step).

  Inductive skip_head_step : tm -> tm -> Prop :=
  | sst_skip v:
    skip_head_step (tskip (tv v)) (tv v).
  Notation skip_step := (ctx_closure skip_head_step).

  Inductive head_step : tm -> tm -> Prop :=
  | st_beta t1 v2:
    head_step (tapp (tv (vabs t1)) (tv v2)) (t1.|[v2/])
  | st_proj v l p:
    v @ l ↘ dpt p →
    head_step (tproj (tv v) l) (path2tm p)
  | st_skip v:
    head_step (tskip (tv v)) (tv v)
  | st_un u v1 v:
    un_op_eval u v1 = Some v →
    head_step (tun u (tv v1)) (tv v)
  | st_bin b v1 v2 v:
    bin_op_eval b v1 v2 = Some v →
    head_step (tbin b (tv v1) (tv v2)) (tv v)
  | st_iftrue e1 e2:
    head_step (tif (tv $ vlit $ lbool true) e1 e2) e1
  | st_iffalse e1 e2:
    head_step (tif (tv $ vlit $ lbool false) e1 e2) e2.
  Notation step := (ctx_closure head_step).

  Global Hint Constructors head_step erased_head_step skip_head_step : core.

  (*
    [head_step] is the sum of [erased_head_step] and [skip_head_step].
    We spell out [head_step] to simplify most proofs on it. *)
  Lemma head_step_skip t1 t2 : head_step t1 t2 ↔ erased_head_step t1 t2 ∨ skip_head_step t1 t2.
  Proof. split; [destruct 1 | destruct 1 as [H|H]; destruct H]; naive_solver. Qed.
  Hint Extern 5 (head_step _ _) => try_once head_step_skip : core.
  (* Hint Resolve -> head_step_skip : core. *)

  Lemma step_skip t1 t2 : step t1 t2 ↔ erased_step t1 t2 ∨ skip_step t1 t2.
  Proof.
    split;
      [destruct 1 as [??? H%head_step_skip]|destruct 1 as [H|H]; destruct H];
      naive_solver.
  Qed.
  Hint Extern 5 (step _ _) => try_once step_skip : core.
  (* Hint Resolve -> step_skip : core. *)
End simpl_red.

(* TODO: add functions converting this back and forth to the standard definitions. *)
Module simpl_red_compat.
End simpl_red_compat.

Import simpl_red.

Module unstutter_skip.

Fixpoint count_skip t :=
  match t with
  | tv _ => 0
  | tapp t1 t2 => count_skip t1 + count_skip t2
  | tproj t1 _ => count_skip t1
  | tskip t1 => 1 + count_skip t1
  | tun _ t1 => count_skip t1
  | tbin _ t1 t2 => count_skip t1 + count_skip t2
  | tif t1 t2 t3 => count_skip t1 + count_skip t2 + count_skip t3
  end.

Lemma skip_head_step_dec t1 t2 : skip_head_step t1 t2 → count_skip t1 = S (count_skip t2).
Proof. by destruct 1. Qed.

Definition count_skip_ectx_item K :=
  match K with
  | SkipCtx => 1
  | AppLCtx t1 => count_skip t1
  | BinLCtx _ t1 => count_skip t1
  | IfCtx t1 t2 => count_skip t1 + count_skip t2
  | _ => 0
  end.

Lemma count_skip_fill_item K t :
  count_skip (fill_item K t) = count_skip_ectx_item K + count_skip t.
Proof. case: K => //= *; lia. Qed.

Definition count_skip_ectx Ks := foldr plus 0 (map count_skip_ectx_item Ks).
(* Arguments count_skip_ectx !_ /. *)

Lemma count_skip_ectx_singleton K : count_skip_ectx [K] = count_skip_ectx_item K.
Proof. by rewrite /count_skip_ectx /= plusnO. Qed.

Lemma count_skip_ectx_app Ks1 Ks2 :
  count_skip_ectx (Ks1 ++ Ks2) =
  count_skip_ectx Ks1 + count_skip_ectx Ks2.
Proof.
  rewrite /count_skip_ectx; induction Ks1; first done.
  by rewrite /= {}IHKs1 plus_assoc.
Qed.

Lemma count_skip_fill Ks t :
  count_skip (fill Ks t) = count_skip_ectx Ks + count_skip t.
Proof.
  induction Ks as [|K Ks] using rev_ind; first done.
  rewrite fill_app /= count_skip_fill_item {}IHKs.
  rewrite count_skip_ectx_app count_skip_ectx_singleton.
  lia.
Qed.

Lemma skip_step_dec t1 t2 : skip_step t1 t2 → count_skip t1 = S (count_skip t2).
Proof.
  destruct 1 as [??? Hs%skip_head_step_dec].
  by rewrite !count_skip_fill Hs plusnS.
Qed.

(*
(* From Coq Require Import RelationClasses. *)
Lemma tc_gt m n : tc gt m n ↔ m > n.
Proof. split; last by intros; exact: tc_once. induction 1; [done|lia]. Qed.

(* Lemma rtc_gt m n : rtc gt m n ↔ m > n.
Proof.
  split; last by intros; exact: rtc_once.
  induction 1. using rtc_ind_l. *)

Lemma skip_step_invariant_tc t1 t2 : tc skip_step t1 t2 → count_skip t1 > count_skip t2.
Proof.
  intros Hred; eapply tc_gt, tc_congruence, Hred => {Hred}t1 {}t2 Hs.
  by rewrite (skip_step_dec Hs); lia.
Qed.

Lemma skip_step_converges t1 : ¬ diverges skip_step t1.
Proof.
  (* rewrite /diverges/not. *)
  pose N := count_skip t1.
  intros Hdiv.
  have [t2 /skip_step_invariant_nsteps Hsteps] := diverges_nsteps (N + 1) Hdiv.
  lia.
Qed. *)

Definition is_succ m n := m = S n.

Lemma nsteps_gt i j k : nsteps is_succ i j k ↔ j = i + k.
Proof.
  rewrite /is_succ; split; first by elim => [//|n _ _ z -> _ ->].
  move->. elim: i => [//=|n IHn].
  by eapply nsteps_l, IHn.
Qed.

Lemma skip_step_invariant_nsteps n t1 t2 : nsteps skip_step n t1 t2 → count_skip t1 = n + count_skip t2.
Proof.
  intros Hred; eapply nsteps_gt, nsteps_congruence, Hred => {Hred}t1 {}t2 Hs.
  by rewrite (skip_step_dec Hs).
Qed.

Lemma step_diverges (R : relation tm) t1 t2 : diverges R t1 → R t1 t2 → diverges R t2.
Proof. intros Hdiv Hstep t3 Hsteps. by eapply Hdiv, rtc_l, Hsteps. Qed.

Lemma nsteps_inv_l `(R : relation A) n x z : nsteps R (S n) x z → ∃ y, R x y ∧ nsteps R n y z.
Proof. intros [? [?%nsteps_once_inv]]%(nsteps_plus_inv 1); eauto. Qed.

Lemma step_diverges_real t1 : diverges step t1 → ∃ t2 t3, rtc step t1 t2 ∧ erased_step t2 t3.
Proof.
  move=> Hdiv; move E: (count_skip t1) => N.
  have [t2 Hsteps] := diverges_nsteps (1 + N) Hdiv.
  elim: N t1 Hdiv E t2 Hsteps => [|N IHN] /= t1 Hdiv E.
  - intros t2 [He|Hs]%nsteps_once_inv%step_skip; first naive_solver.
    by move: Hs => /skip_step_dec; rewrite {}E.
  - intros t5 [t2 [[He|Hstep12]%step_skip Hsteps]]%nsteps_inv_l;
      first naive_solver.
    have := skip_step_dec Hstep12; rewrite {}E => -[Hs']; subst N.
    have {}Hdiv: diverges step t2 by apply: step_diverges; eauto.
    have {IHN} [t3 [t4 [Hstep23 Hstep34]]] := IHN t2 Hdiv eq_refl _ Hsteps.
    suff Hstep13: rtc step t1 t3; naive_solver.
Qed.
End unstutter_skip.
