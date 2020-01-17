(** Lemmas relating is_unstamped with binding and substitution. *)
From D.Dot Require Import syn synLemmas traversals.
From D.Dot Require Export stampingDefsCore closed_subst.
Import Trav1.

Set Implicit Arguments.

Implicit Types
         (T: ty) (v: vl) (e: tm) (p: path) (d: dm) (ds: dms) (vs: vls)
         (Γ : ctx) (g: stys) (n: nat).

Definition is_unstamped_sub n m b s :=
  ∀ i, i < n → is_unstamped_vl m b (s i).
Notation is_unstamped_ren n m b r := (is_unstamped_sub n m b (ren r)).

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
    (* firsorder is slower. *)
    (* firstorder eauto using eq_up. *)
      try first [eapply H|eapply H0|eapply H1]; eauto using eq_up.
  - apply fv_vobj, nclosed_axs_to_nclosed.
    generalize dependent ds => ds.
    rewrite !Forall_fmap => *.
    decompose_Forall; case_match; subst. eauto.
Qed.

Lemma is_unstamped_nclosed_tm e n b: is_unstamped_tm n b e → nclosed e n.
Proof. apply is_unstamped_nclosed_mut. Qed.
Lemma is_unstamped_nclosed_vl v n b: is_unstamped_vl n b v → nclosed_vl v n.
Proof. apply is_unstamped_nclosed_mut. Qed.
Lemma is_unstamped_nclosed_dm d n b: is_unstamped_dm n b d → nclosed d n.
Proof. apply is_unstamped_nclosed_mut. Qed.
Lemma is_unstamped_nclosed_path p n b: is_unstamped_path n b p → nclosed p n.
Proof. apply is_unstamped_nclosed_mut. Qed.
Lemma is_unstamped_nclosed_ty T n b: is_unstamped_ty n b T → nclosed T n.
Proof. apply is_unstamped_nclosed_mut. Qed.

Hint Resolve is_unstamped_nclosed_tm is_unstamped_nclosed_vl
  is_unstamped_nclosed_dm is_unstamped_nclosed_path
  is_unstamped_nclosed_ty : core.

Lemma is_unstamped_nclosed_σ σ i b:
  is_unstamped_σ i b σ →
  nclosed_σ σ i.
Proof. intros; decompose_Forall. exact: is_unstamped_nclosed_vl. Qed.
Hint Resolve is_unstamped_nclosed_ty is_unstamped_nclosed_σ : core.

Lemma is_unstamped_nclosed_sub n m b ξ :
  is_unstamped_sub n m b ξ → nclosed_sub n m ξ.
Proof. move => Hst i Hle. apply /is_unstamped_nclosed_vl /Hst/Hle. Qed.

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

Lemma is_unstamped_weaken_tm e__s m n b:
  is_unstamped_tm m b e__s →
  m <= n →
  is_unstamped_tm n b e__s.
Proof. apply (is_unstamped_weaken_mut). Qed.
Lemma is_unstamped_weaken_vl v__s m n b:
  is_unstamped_vl m b v__s →
  m <= n →
  is_unstamped_vl n b v__s.
Proof. apply (is_unstamped_weaken_mut). Qed.
Lemma is_unstamped_weaken_dm d__s m n b:
  is_unstamped_dm m b d__s →
  m <= n →
  is_unstamped_dm n b d__s.
Proof. apply (is_unstamped_weaken_mut). Qed.
Lemma is_unstamped_weaken_path p__s m n b:
  is_unstamped_path m b p__s →
  m <= n →
  is_unstamped_path n b p__s.
Proof. apply (is_unstamped_weaken_mut). Qed.
Lemma is_unstamped_weaken_ty T__s m n b:
  is_unstamped_ty m b T__s →
  m <= n →
  is_unstamped_ty n b T__s.
Proof. apply (is_unstamped_weaken_mut). Qed.

Lemma is_unstamped_weaken_σ σ m n b:
  is_unstamped_σ m b σ →
  m <= n →
  is_unstamped_σ n b σ.
Proof. intros; decompose_Forall. exact: is_unstamped_weaken_vl. Qed.

Lemma is_unstamped_idsσ_ren m n j b: j + n <= m → is_unstamped_σ m b (idsσ n).|[ren (+j)].
Proof.
  elim: n m j => [//=|n IHn] m j Ijm.
  cbn; rewrite (hren_upn_gen 0 1 j) /= plusnO.
  repeat constructor => //=; first lia.
  apply IHn; lia.
Qed.

Lemma is_unstamped_idsσ m n b: n <= m → is_unstamped_σ m b (idsσ n).
Proof. pose proof (@is_unstamped_idsσ_ren m n 0) as H. asimpl in H. exact: H. Qed.
Hint Resolve is_unstamped_idsσ : core.

Lemma is_unstamped_ren_shift n m j b:
  m >= j + n → is_unstamped_ren n m b (+j).
Proof. constructor => //=; lia. Qed.

Lemma is_unstamped_ren_up n m r b:
  is_unstamped_ren n m b r →
  is_unstamped_ren (S n) (S m) b (upren r).
Proof.
  (* rewrite /is_unstamped_ren /is_unstamped_sub /=. *)
  move => Hr [|i] //= Hi; first by constructor => /=; lia.
  have Hi': i < n by lia.
  specialize (Hr i Hi'); inverse Hr.
  constructor; cbn in *; by lia.
Qed.
Hint Resolve is_unstamped_ren_up is_unstamped_ren_shift : core.

From D.Dot Require Import closed_subst.

Lemma is_unstamped_nclosed_ren i j r b: is_unstamped_ren i j b r → nclosed_ren i j r.
Proof.
  move => /= Hr x Hx. specialize (Hr x Hx); inverse Hr. exact: nclosed_vl_ids.
Qed.

Lemma is_unstamped_ren_var v r:
  (∃ x : var, v = var_vl x) →
  ∃ x : var, rename r v = var_vl x.
Proof. naive_solver. Qed.

Lemma is_unstamped_var_intype i j b :
  is_unstamped_vl i b (ids j) → is_unstamped_vl i InType (ids j).
Proof. inversion 1; by constructor. Qed.
Lemma is_unstamped_ren_intype i j b r :
  is_unstamped_ren i j b r → is_unstamped_ren i j InType r.
Proof. intros Hu ?**. by eapply is_unstamped_var_intype, Hu. Qed.

Hint Extern 0 (forall_traversal_tm _ _ _)   => progress cbn : core.
Hint Extern 0 (forall_traversal_vl _ _ _)   => progress cbn : core.
Hint Extern 0 (forall_traversal_dm _ _ _)   => progress cbn : core.
Hint Extern 0 (forall_traversal_path _ _ _) => progress cbn : core.
Hint Extern 0 (forall_traversal_ty _ _ _)   => progress cbn : core.

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
    cbn in *; try by [|naive_solver eauto using is_unstamped_ren_var, is_unstamped_ren_intype].
  - constructor; rewrite list_pair_swap_snd_rename Forall_fmap;
      by decompose_Forall; eauto.
Qed.

Lemma is_unstamped_ren_vl v r i j b:
  is_unstamped_ren i j b r →
  is_unstamped_vl i b v →
  is_unstamped_vl j b (rename r v).
Proof. apply is_unstamped_ren_mut. Qed.

Lemma is_unstamped_sub_up n m s b:
  is_unstamped_sub n m b s →
  is_unstamped_sub (S n) (S m) b (up s).
Proof.
  move => Hs [|i] Hi //=. by constructor => /=; lia.
  eapply is_unstamped_ren_vl; eauto with lia.
Qed.
Hint Resolve is_unstamped_sub_up : core.

(* False! Hence is_unstamped_sub_mut is also false. *)
(* Lemma is_unstamped_sub_varpath p s i j:
  is_unstamped_sub i j s →
  is_unstamped_path i p →
  (∃ x : var, path_root p = var_vl x) →
  ∃ x : var, path_root p.|[s] = var_vl x.
Proof.
  intros Hus Hup [x ?]. induction p as [[]|]; simplify_eq/=;
    with_is_unstamped inverse. 2: eauto.
    inverse H1; cbn in *.
  specialize (Hus x H2). inverse Hus; simplify_eq/=.
  eauto.
Abort. *)

(*
Lemma is_unstamped_sub_mut:
  (∀ t s i j,
    is_unstamped_sub i j s →
    is_unstamped_tm i b t →
    is_unstamped_tm j b t.|[s]) ∧
  (∀ v s i j,
    is_unstamped_sub i j s →
    is_unstamped_vl i v →
    is_unstamped_vl j v.[s]) ∧
  (∀ d s i j,
    is_unstamped_sub i j s →
    is_unstamped_dm i d →
    is_unstamped_dm j d.|[s]) ∧
  (∀ p s i j,
    is_unstamped_sub i j s →
    is_unstamped_path i p →
    is_unstamped_path j p.|[s]) ∧
  (∀ T s i j,
    is_unstamped_sub i j s →
    is_unstamped_ty i T →
    is_unstamped_ty j T.|[s]).
Proof.
  apply syntax_mut_ind; intros;
    with_is_unstamped ltac:(fun H => inversion_clear H);
    cbn in *; try by [|constructor; cbn; eauto 3].
  - eauto.
  - constructor => /=.
    repeat rewrite ->Forall_fmap in *; rewrite !Forall_fmap.
    decompose_Forall.
    unfold snd in *; case_match; subst; cbn; eauto.
  - constructor; cbn; eauto.
Abort. *)

(* Lemma is_unstamped_sub_vl v s m n:
  is_unstamped_sub n m s →
  is_unstamped_vl n v →
  is_unstamped_vl m v.[s].
Proof. apply is_unstamped_sub_mut. Qed.
Lemma is_unstamped_sub_ty T s m n:
  is_unstamped_sub n m s →
  is_unstamped_ty n T →
  is_unstamped_ty m T.|[s].
Proof. apply is_unstamped_sub_mut. Qed.

Lemma is_unstamped_sub_σ σ s m n:
  is_unstamped_sub n m s →
  is_unstamped_σ n σ →
  is_unstamped_σ m σ.|[s].
Proof.
  intros; rewrite Forall_fmap. decompose_Forall. exact: is_unstamped_sub_vl.
Qed. *)

Lemma is_unstamped_vl_ids i j b: i < j → is_unstamped_vl j b (ids i).
Proof. rewrite /ids /ids_vl; by constructor. Qed.
Hint Resolve is_unstamped_vl_ids : core.

Lemma is_unstamped_sub_stail i j v sb b:
  is_unstamped_sub (S i) j b (v .: sb) →
  is_unstamped_sub i j b sb.
Proof. move => Hs k Hle. apply (Hs (S k)), lt_n_S, Hle. Qed.

Lemma is_unstamped_sub_equiv {σ i b} :
  is_unstamped_σ i b σ ↔ is_unstamped_sub (length σ) i b (to_subst σ).
Proof.
  split; elim: σ => [//| /= v σ IHσ] Hcl/=.
  - by move => ??; lia.
  - inverse Hcl. move => [//|j /lt_S_n] /=. exact: IHσ.
  - constructor. by apply (Hcl 0); lia.
    eapply IHσ, is_unstamped_sub_stail, Hcl.
Qed.
Hint Resolve -> is_unstamped_sub_equiv : core.


Lemma is_unstamped_sub_single n v b:
  is_unstamped_vl n b v →
  is_unstamped_sub (S n) n b (v .: ids).
Proof. move => Hv [|i] Hin /=; eauto with lia. Qed.

Lemma is_unstamped_sub_ren_ty T r i j b:
  is_unstamped_ren i j b r →
  is_unstamped_ty i b T → is_unstamped_ty j b T.|[ren r].
Proof. rewrite -ty_rename_Lemma. apply is_unstamped_ren_mut. Qed.

Lemma is_unstamped_sub_ren_path p r i j b:
  is_unstamped_ren i j b r →
  is_unstamped_path i b p → is_unstamped_path j b p.|[ren r].
Proof. rewrite -path_rename_Lemma. apply is_unstamped_ren_mut. Qed.


Lemma is_unstamped_ren1 i b : is_unstamped_ren i (S i) b (+1).
Proof. apply is_unstamped_ren_shift; lia. Qed.
Hint Resolve is_unstamped_ren1 : core.

Lemma is_unstamped_ren1_ty i T b:
  is_unstamped_ty i b T ->
  is_unstamped_ty (S i) b (T.|[ren (+1)]).
Proof. exact: is_unstamped_sub_ren_ty. Qed.

Lemma is_unstamped_ren1_path i p b:
  is_unstamped_path i b p ->
  is_unstamped_path (S i) b (shift p).
Proof. exact: is_unstamped_sub_ren_path. Qed.


Lemma is_unstamped_sub_rev_var v s:
  (∃ x : var, v.[s] = var_vl x) →
  ∃ x : var, v = var_vl x.
Proof. intros [x ?]; destruct v; simplify_eq; eauto. Qed.

Lemma is_unstamped_sub_rev_mut:
  (∀ e i,
    nclosed e i →
    ∀ s j b,
    is_unstamped_tm j b (e.|[s]) →
    is_unstamped_tm i b e) ∧
  (∀ v i,
    nclosed_vl v i →
    ∀ s j b,
    is_unstamped_vl j b (v.[s]) →
    is_unstamped_vl i b v) ∧
  (∀ d i,
    nclosed d i →
    ∀ s j b,
    is_unstamped_dm j b (d.|[s]) →
    is_unstamped_dm i b d) ∧
  (∀ p i,
    nclosed p i →
    ∀ s j b,
    is_unstamped_path j b (p.|[s]) →
    is_unstamped_path i b p) ∧
  (∀ T i,
    nclosed T i →
    ∀ s j b,
    is_unstamped_ty j b (T.|[s]) →
    is_unstamped_ty i b T).
Proof.
  apply nclosed_syntax_mut_ind => /=; intros;
    with_is_unstamped ltac:(fun H => try nosplit (inverse H)); ev;
    try by [| constructor;
      eauto 3 using eq_up, is_unstamped_sub_rev_var with lia].
  - auto using nclosed_var_lt.
  - unfold hsubst, list_hsubst in *.
    constructor => /=.
    rewrite ->?@Forall_fmap in *.
    decompose_Forall. destruct x; cbn in *. eauto.
  - constructor; naive_solver eauto using is_unstamped_sub_rev_var.
Qed.

Lemma is_unstamped_sub_rev_vl v s i j b:
  nclosed_vl v i →
  is_unstamped_vl j b (v.[s]) →
  is_unstamped_vl i b v.
Proof. unmut_lemma is_unstamped_sub_rev_mut. Qed.
Lemma is_unstamped_sub_rev_ty T s i j b:
  nclosed T i →
  is_unstamped_ty j b (T.|[s]) →
  is_unstamped_ty i b T.
Proof. unmut_lemma is_unstamped_sub_rev_mut. Qed.

Lemma is_unstamped_sub_one_rev i b T v:
  nclosed T (S i) →
  is_unstamped_ty i b (T.|[v/]) →
  is_unstamped_ty (S i) b T.
Proof. intros; by eapply is_unstamped_sub_rev_ty. Qed.

Lemma is_unstamped_ren_ty i b T:
  is_unstamped_ty i b T <->
  is_unstamped_ty (S i) b (T.|[ren (+1)]).
Proof.
  split; first exact: is_unstamped_ren1_ty.
  intros Hu.
  eapply is_unstamped_sub_rev_ty, Hu.
  eapply nclosed_ren_inv_ty_one, is_unstamped_nclosed_ty, Hu.
Qed.
