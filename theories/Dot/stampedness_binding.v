(** Lemmas relating is_stamped with binding and substitution. *)
From D.Dot Require Import syn synLemmas traversals.
From D.Dot Require Export stampingDefsCore.
Import Trav1.

Set Implicit Arguments.

Implicit Types
         (T: ty) (v: vl) (e: tm) (p: path) (d: dm) (ds: dms) (vs: vls)
         (Γ : ctx) (g: stys) (n: nat).

Definition is_stamped_sub n m g s :=
  ∀ i, i < n → is_stamped_vl m g (s i).
Notation is_stamped_ren n m g r := (is_stamped_sub n m g (ren r)).

Lemma is_stamped_nclosed_mut g:
  (∀ t i,
    is_stamped_tm i g t →
    nclosed t i) ∧
  (∀ v i,
    is_stamped_vl i g v →
    nclosed_vl v i) ∧
  (∀ d i,
    is_stamped_dm i g d →
    nclosed d i) ∧
  (∀ p i,
    is_stamped_path i g p →
    nclosed p i) ∧
  (∀ T i,
    is_stamped_ty i g T →
    nclosed T i).
Proof.
  apply syntax_mut_ind; intros; with_is_stamped inverse => //; ev;
    try by move => s1 s2 Hseq; f_equal/=;
      try first [eapply H|eapply H0]; eauto using eq_up.
  - apply fv_vobj, nclosed_axs_to_nclosed.
    generalize dependent ds => ds.
    rewrite !Forall_fmap => *.
    decompose_Forall; case_match; subst. eauto.
  - apply fv_dtysem. decompose_Forall. by eauto.
Qed.

Lemma is_stamped_nclosed_vl v g i:
  is_stamped_vl i g v →
  nclosed_vl v i.
Proof. apply (is_stamped_nclosed_mut g). Qed.
Lemma is_stamped_nclosed_ty T g i:
  is_stamped_ty i g T →
  nclosed T i.
Proof. apply (is_stamped_nclosed_mut g). Qed.

Lemma is_stamped_nclosed_σ σ g i:
  is_stamped_σ i g σ →
  nclosed_σ σ i.
Proof. intros; decompose_Forall. exact: is_stamped_nclosed_vl. Qed.
Hint Resolve is_stamped_nclosed_ty is_stamped_nclosed_σ : core.

Lemma is_stamped_nclosed_sub n m g ξ :
  is_stamped_sub n m g ξ → nclosed_sub n m ξ.
Proof. move => Hst i Hle. apply /is_stamped_nclosed_vl /Hst/Hle. Qed.

Lemma is_stamped_weaken_mut g:
  (∀ e__s m n,
      is_stamped_tm m g e__s →
      m <= n →
      is_stamped_tm n g e__s) ∧
  (∀ v__s m n,
      is_stamped_vl m g v__s →
      m <= n →
      is_stamped_vl n g v__s) ∧
  (∀ d__s m n,
      is_stamped_dm m g d__s →
      m <= n →
      is_stamped_dm n g d__s) ∧
  (∀ p__s m n,
      is_stamped_path m g p__s →
      m <= n →
      is_stamped_path n g p__s) ∧
  (∀ T__s m n,
      is_stamped_ty m g T__s →
      m <= n →
      is_stamped_ty n g T__s).
Proof.
  apply syntax_mut_ind;
    by [intros; with_is_stamped inverse; econstructor;
      decompose_Forall; eauto with lia].
Qed.

Lemma is_stamped_weaken_tm g e__s m n:
  is_stamped_tm m g e__s →
  m <= n →
  is_stamped_tm n g e__s.
Proof. apply (is_stamped_weaken_mut g). Qed.
Lemma is_stamped_weaken_vl g v__s m n:
  is_stamped_vl m g v__s →
  m <= n →
  is_stamped_vl n g v__s.
Proof. apply (is_stamped_weaken_mut g). Qed.
Lemma is_stamped_weaken_dm g d__s m n:
  is_stamped_dm m g d__s →
  m <= n →
  is_stamped_dm n g d__s.
Proof. apply (is_stamped_weaken_mut g). Qed.
Lemma is_stamped_weaken_path g p__s m n:
  is_stamped_path m g p__s →
  m <= n →
  is_stamped_path n g p__s.
Proof. apply (is_stamped_weaken_mut g). Qed.
Lemma is_stamped_weaken_ty g T__s m n:
  is_stamped_ty m g T__s →
  m <= n →
  is_stamped_ty n g T__s.
Proof. apply (is_stamped_weaken_mut g). Qed.

Lemma is_stamped_weaken_σ g σ m n:
  is_stamped_σ m g σ →
  m <= n →
  is_stamped_σ n g σ.
Proof. intros; decompose_Forall. exact: is_stamped_weaken_vl. Qed.

Lemma is_stamped_idsσ_ren g m n j: j + n <= m → is_stamped_σ m g (idsσ n).|[ren (+j)].
Proof.
  elim: n m j => [//=|n IHn] m j Ijm.
  cbn; rewrite (hren_upn_gen 0 1 j) /= plusnO.
  repeat constructor => //=; first lia.
  apply IHn; lia.
Qed.

Lemma is_stamped_idsσ g m n: n <= m → is_stamped_σ m g (idsσ n).
Proof. pose proof (@is_stamped_idsσ_ren g m n 0) as H. asimpl in H. exact: H. Qed.
Hint Resolve is_stamped_idsσ : core.

Lemma is_stamped_ren_shift n m j g:
  m >= j + n → is_stamped_ren n m g (+j).
Proof. constructor => //=; lia. Qed.

Lemma is_stamped_ren_up n m g r:
  is_stamped_ren n m g r →
  is_stamped_ren (S n) (S m) g (upren r).
Proof.
  (* rewrite /is_stamped_ren /is_stamped_sub /=. *)
  move => Hr [|i] //= Hi; first by constructor => /=; lia.
  have Hi': i < n by lia.
  specialize (Hr i Hi'); inverse Hr.
  constructor; cbn in *; by lia.
Qed.
Hint Resolve is_stamped_ren_up is_stamped_ren_shift : core.

From D.Dot Require Import closed_subst.

Lemma is_stamped_nclosed_ren i j g r: is_stamped_ren i j g r → nclosed_ren i j r.
Proof.
  move => /= Hr x Hx. specialize (Hr x Hx); inverse Hr. exact: nclosed_vl_ids.
Qed.

Lemma is_stamped_ren_mut:
  (∀ t g r i j,
    is_stamped_ren i j g r →
    is_stamped_tm i g t →
    is_stamped_tm j g (rename r t)) ∧
  (∀ v g r i j,
    is_stamped_ren i j g r →
    is_stamped_vl i g v →
    is_stamped_vl j g (rename r v)) ∧
  (∀ d g r i j,
    is_stamped_ren i j g r →
    is_stamped_dm i g d →
    is_stamped_dm j g (rename r d)) ∧
  (∀ p g r i j,
    is_stamped_ren i j g r →
    is_stamped_path i g p →
    is_stamped_path j g (rename r p)) ∧
  (∀ T g r i j,
    is_stamped_ren i j g r →
    is_stamped_ty i g T →
    is_stamped_ty j g (rename r T)).
Proof.
  apply syntax_mut_ind; intros; with_is_stamped ltac:(fun H => inversion_clear H);
    cbn in *; try by [constructor; cbn; eauto].
  - eauto.
  - constructor; rewrite list_pair_swap_snd_rename Forall_fmap;
      by decompose_Forall; eauto.
  - eapply @trav_dtysem with (ts' := ts') (T' := T'); ev; subst;
      rewrite //= ?map_length ?Forall_fmap.
    by split_and!.
    by decompose_Forall; eauto.
Qed.

Lemma is_stamped_ren_vl v g r i j:
  is_stamped_ren i j g r →
  is_stamped_vl i g v →
  is_stamped_vl j g (rename r v).
Proof. apply is_stamped_ren_mut. Qed.

Lemma is_stamped_sub_up n m g s:
  is_stamped_sub n m g s →
  is_stamped_sub (S n) (S m) g (up s).
Proof.
  move => Hs [|i] Hi //=. by constructor => /=; lia.
  eapply is_stamped_ren_vl; eauto with lia.
Qed.
Hint Resolve is_stamped_sub_up : core.

Lemma is_stamped_sub_mut:
  (∀ t g s i j,
    is_stamped_sub i j g s →
    is_stamped_tm i g t →
    is_stamped_tm j g t.|[s]) ∧
  (∀ v g s i j,
    is_stamped_sub i j g s →
    is_stamped_vl i g v →
    is_stamped_vl j g v.[s]) ∧
  (∀ d g s i j,
    is_stamped_sub i j g s →
    is_stamped_dm i g d →
    is_stamped_dm j g d.|[s]) ∧
  (∀ p g s i j,
    is_stamped_sub i j g s →
    is_stamped_path i g p →
    is_stamped_path j g p.|[s]) ∧
  (∀ T g s i j,
    is_stamped_sub i j g s →
    is_stamped_ty i g T →
    is_stamped_ty j g T.|[s]).
Proof.
  apply syntax_mut_ind; intros; with_is_stamped ltac:(fun H => inversion_clear H);
    cbn in *; try by [constructor; cbn; eauto]; eauto.
  - constructor => /=.
    repeat rewrite ->Forall_fmap in *; rewrite !Forall_fmap.
    decompose_Forall.
    unfold snd in *; case_match; subst; cbn; eauto.
  - eapply @trav_dtysem with (ts' := ts') (T' := T'); ev; subst;
      rewrite //= ?map_length ?Forall_fmap.
    by split_and!.
    by decompose_Forall; eauto.
Qed.

Lemma is_stamped_sub_vl v g s m n:
  is_stamped_sub n m g s →
  is_stamped_vl n g v →
  is_stamped_vl m g v.[s].
Proof. apply is_stamped_sub_mut. Qed.
Lemma is_stamped_sub_ty T g s m n:
  is_stamped_sub n m g s →
  is_stamped_ty n g T →
  is_stamped_ty m g T.|[s].
Proof. apply is_stamped_sub_mut. Qed.

Lemma is_stamped_sub_σ σ g s m n:
  is_stamped_sub n m g s →
  is_stamped_σ n g σ →
  is_stamped_σ m g σ.|[s].
Proof.
  intros; rewrite Forall_fmap. decompose_Forall. exact: is_stamped_sub_vl.
Qed.

Lemma is_stamped_vl_ids g i j: i < j → is_stamped_vl j g (ids i).
Proof. rewrite /ids /ids_vl; by constructor. Qed.
Hint Resolve is_stamped_vl_ids : core.

Lemma is_stamped_sub_stail i j v sb g:
  is_stamped_sub (S i) j g (v .: sb) →
  is_stamped_sub i j g sb.
Proof. move => Hs k Hle. apply (Hs (S k)), lt_n_S, Hle. Qed.

Lemma is_stamped_sub_equiv {σ g i} :
  is_stamped_σ i g σ ↔ is_stamped_sub (length σ) i g (to_subst σ).
Proof.
  split; elim: σ => [//| /= v σ IHσ] Hcl/=.
  - by move => ??; lia.
  - inverse Hcl. move => [//|j /lt_S_n] /=. exact: IHσ.
  - constructor. by apply (Hcl 0); lia.
    eapply IHσ, is_stamped_sub_stail, Hcl.
Qed.
Hint Resolve -> is_stamped_sub_equiv : core.


Lemma is_stamped_sub_single n v g:
  is_stamped_vl n g v →
  is_stamped_sub (S n) n g (v .: ids).
Proof. move => Hv [|i] Hin /=; eauto with lia. Qed.

Lemma is_stamped_sub_one n T v g:
  is_stamped_ty (S n) g T →
  is_stamped_vl n g v →
  is_stamped_ty n g (T.|[v/]).
Proof.
  intros; eapply is_stamped_sub_ty => //. exact: is_stamped_sub_single.
Qed.

Lemma is_stamped_ren1 i g : is_stamped_ren i (S i) g (+1).
Proof. apply is_stamped_ren_shift; auto. Qed.
Hint Resolve is_stamped_ren1 : core.

Lemma is_stamped_ren1_ty i T g:
  is_stamped_ty i g T ->
  is_stamped_ty (S i) g (T.|[ren (+1)]).
Proof. exact: is_stamped_sub_ty. Qed.

Lemma is_stamped_sub_rev_mut g:
  (∀ e i,
    nclosed e i →
    ∀ s j,
    is_stamped_tm j g (e.|[s]) →
    is_stamped_tm i g e) ∧
  (∀ v i,
    nclosed_vl v i →
    ∀ s j,
    is_stamped_vl j g (v.[s]) →
    is_stamped_vl i g v) ∧
  (∀ d i,
    nclosed d i →
    ∀ s j,
    is_stamped_dm j g (d.|[s]) →
    is_stamped_dm i g d) ∧
  (∀ p i,
    nclosed p i →
    ∀ s j,
    is_stamped_path j g (p.|[s]) →
    is_stamped_path i g p) ∧
  (∀ T i,
    nclosed T i →
    ∀ s j,
    is_stamped_ty j g (T.|[s]) →
    is_stamped_ty i g T).
Proof.
  apply nclosed_syntax_mut_ind => /=; intros;
    try by with_is_stamped inverse; ev;
    constructor => /=; eauto using eq_up with lia.
  - auto using nclosed_var_lt.
  - with_is_stamped inverse; cbn in *; ev.
    unfold hsubst, list_hsubst in *.
    constructor => /=.
    rewrite ->?@Forall_fmap in *.
    decompose_Forall. destruct x; cbn in *. eauto.
  - with_is_stamped inverse; cbn in *.
    unfold hsubst, list_hsubst in *; rewrite -> @Forall_fmap in *.
    eapply @trav_dtysem with (ts' := ts') (T' := T'); ev; subst => //=;
      rewrite //= ?map_length.
    by split_and!.
    by decompose_Forall; eauto.
Qed.

Lemma is_stamped_sub_rev_vl g v s i j:
  nclosed_vl v i →
  is_stamped_vl j g (v.[s]) →
  is_stamped_vl i g v.
Proof. unmut_lemma (is_stamped_sub_rev_mut g). Qed.
Lemma is_stamped_sub_rev_ty g T s i j:
  nclosed T i →
  is_stamped_ty j g (T.|[s]) →
  is_stamped_ty i g T.
Proof. unmut_lemma (is_stamped_sub_rev_mut g). Qed.

Lemma is_stamped_sub_one_rev i T v g:
  nclosed T (S i) →
  is_stamped_ty i g (T.|[v/]) →
  is_stamped_ty (S i) g T.
Proof. intros; by eapply is_stamped_sub_rev_ty. Qed.

Lemma is_stamped_ren_ty i T g:
  nclosed T i →
  is_stamped_ty i g T <->
  is_stamped_ty (S i) g (T.|[ren (+1)]).
Proof.
  split; [ exact: is_stamped_sub_ty | exact: is_stamped_sub_rev_ty ].
Qed.
