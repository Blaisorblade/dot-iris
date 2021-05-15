(** Lemmas relating is_unstamped with binding and substitution. *)
From D.Dot Require Import syn traversals.
From D.Dot Require Export core_stamping_defs.
Import Trav1.

Set Implicit Arguments.

Implicit Types
         (T: ty) (v: vl) (e: tm) (p: path) (d: dm) (ds: dms) (vs: vls)
         (Γ : ctx) (n: nat).

Definition is_unstamped_sub n m b s :=
  ∀ i, i < n → is_unstamped_vl m b (s i).
Notation is_unstamped_ren n m b r := (is_unstamped_sub n m b (ren r)).

Lemma fv_vobj ds n: nclosed ds n.+1 → nclosed_vl (vobj ds) n.
Proof. solve_fv_congruence. Qed.

Lemma is_unstamped_nclosed_mut:
  (∀ t i b,
    is_unstamped_tm i b t →
    nclosed t i) ∧
  (∀ v i b,
    is_unstamped_vl i b v →
    nclosed_vl v i) ∧
  (∀ d i b,
    is_unstamped_dm i b d →
    nclosed d i) ∧
  (∀ p i b,
    is_unstamped_path i b p →
    nclosed p i) ∧
  (∀ T i b,
    is_unstamped_ty i b T →
    nclosed T i).
Proof.
  apply syntax_mut_ind; intros; with_is_unstamped inverse => //; ev;
    try by move => s1 s2 Hseq; f_equal/=;
      try first [eapply H|eapply H0|eapply H1]; eauto using eq_up.
  - apply fv_vobj, nclosed_axs_to_nclosed.
    generalize dependent ds => ds.
    rewrite !Forall_fmap => *.
    decompose_Forall; case_match; subst. eauto.
Qed.

Lemma is_unstamped_nclosed_path p n b: is_unstamped_path n b p → nclosed p n.
Proof. apply is_unstamped_nclosed_mut. Qed.
Lemma is_unstamped_nclosed_ty T n b: is_unstamped_ty n b T → nclosed T n.
Proof. apply is_unstamped_nclosed_mut. Qed.

#[global] Hint Resolve is_unstamped_nclosed_path is_unstamped_nclosed_ty : core.

Lemma is_unstamped_weaken_mut:
  (∀ e__s m n b,
      is_unstamped_tm m b e__s →
      m <= n →
      is_unstamped_tm n b e__s) ∧
  (∀ v__s m n b,
      is_unstamped_vl m b v__s →
      m <= n →
      is_unstamped_vl n b v__s) ∧
  (∀ d__s m n b,
      is_unstamped_dm m b d__s →
      m <= n →
      is_unstamped_dm n b d__s) ∧
  (∀ p__s m n b,
      is_unstamped_path m b p__s →
      m <= n →
      is_unstamped_path n b p__s) ∧
  (∀ T__s m n b,
      is_unstamped_ty m b T__s →
      m <= n →
      is_unstamped_ty n b T__s).
Proof.
  apply syntax_mut_ind;
    by [intros; with_is_unstamped inverse; econstructor;
      decompose_Forall; eauto with lia].
Qed.

Lemma is_unstamped_weaken_ty T__s m n b:
  is_unstamped_ty m b T__s →
  m <= n →
  is_unstamped_ty n b T__s.
Proof. apply is_unstamped_weaken_mut. Qed.

Lemma is_unstamped_ren_shift n m j b:
  m >= j + n → is_unstamped_ren n m b (+j).
Proof. constructor => //=; lia. Qed.

Lemma is_unstamped_ren1 i b : is_unstamped_ren i i.+1 b (+1).
Proof. apply is_unstamped_ren_shift; lia. Qed.
#[global] Hint Resolve is_unstamped_ren1 : core.

Lemma is_unstamped_ren_up n m r b:
  is_unstamped_ren n m b r →
  is_unstamped_ren n.+1 m.+1 b (upren r).
Proof.
  move => Hr [|i] //= Hi; first by constructor => /=; lia.
  have Hi': i < n by lia.
  specialize (Hr i Hi'); inverse Hr.
  constructor; cbn in *; by lia.
Qed.
#[global] Hint Resolve is_unstamped_ren_up is_unstamped_ren_shift : core.

Lemma is_unstamped_ren_var v r:
  (∃ x : var, v = vvar x) →
  ∃ x : var, rename r v = vvar x.
Proof. naive_solver. Qed.

Lemma is_unstamped_var_OnlyVars i j b :
  is_unstamped_vl i b (ids j) → is_unstamped_vl i OnlyVars (ids j).
Proof. inversion 1; by constructor. Qed.
Lemma is_unstamped_ren_OnlyVars i j b r :
  is_unstamped_ren i j b r → is_unstamped_ren i j OnlyVars r.
Proof. intros Hu ?**. by eapply is_unstamped_var_OnlyVars, Hu. Qed.

Lemma is_unstamped_ren_mut:
  (∀ t r i j b,
    is_unstamped_ren i j b r →
    is_unstamped_tm i b t →
    is_unstamped_tm j b (rename r t)) ∧
  (∀ v r i j b,
    is_unstamped_ren i j b r →
    is_unstamped_vl i b v →
    is_unstamped_vl j b (rename r v)) ∧
  (∀ d r i j b,
    is_unstamped_ren i j b r →
    is_unstamped_dm i b d →
    is_unstamped_dm j b (rename r d)) ∧
  (∀ p r i j b,
    is_unstamped_ren i j b r →
    is_unstamped_path i b p →
    is_unstamped_path j b (rename r p)) ∧
  (∀ T r i j b,
    is_unstamped_ren i j b r →
    is_unstamped_ty i b T →
    is_unstamped_ty j b (rename r T)).
Proof.
  apply syntax_mut_ind; intros; with_is_unstamped ltac:(fun H => inversion_clear H);
    cbn in *; try by [|naive_solver eauto using is_unstamped_ren_var, is_unstamped_ren_OnlyVars].
  - constructor; rewrite list_pair_swap_snd_rename Forall_fmap;
      by decompose_Forall; eauto.
  - constructor; naive_solver.
Qed.

Lemma is_unstamped_sub_ren_ty T r i j b:
  is_unstamped_ren i j b r →
  is_unstamped_ty i b T → is_unstamped_ty j b T.|[ren r].
Proof. rewrite -ty_rename_Lemma. apply is_unstamped_ren_mut. Qed.

Lemma is_unstamped_sub_ren_path p r i j b:
  is_unstamped_ren i j b r →
  is_unstamped_path i b p → is_unstamped_path j b p.|[ren r].
Proof. rewrite -path_rename_Lemma. apply is_unstamped_ren_mut. Qed.


Lemma is_unstamped_ren1_ty i T b:
  is_unstamped_ty i b T →
  is_unstamped_ty i.+1 b (shift T).
Proof. exact: is_unstamped_sub_ren_ty. Qed.

Lemma is_unstamped_ren1_path i p b:
  is_unstamped_path i b p →
  is_unstamped_path i.+1 b (shift p).
Proof. exact: is_unstamped_sub_ren_path. Qed.


(* XXX *)
Lemma is_unstamped_TLater_n {i n T}:
  is_unstamped_ty' n T →
  is_unstamped_ty' n (iterate TLater i T).
Proof. elim: i => [|//i IHi]; rewrite ?iterate_0 ?iterate_S //; auto. Qed.
