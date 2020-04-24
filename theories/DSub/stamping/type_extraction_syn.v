(** *)
From stdpp Require Import gmap fin_map_dom.

From D Require Import tactics.
From D.DSub Require Import syn syn_lemmas.
From D.DSub Require Export core_stamping_defs stampedness_binding.

Set Implicit Arguments.

Implicit Types (T: ty) (v: vl) (e: tm) (Γ : ctx) (g: stys) (n: nat) (s: stamp).

Lemma fresh_stamp_spec {X} (g: gmap stamp X) : fresh_stamp g ∉ gdom g.
Proof. apply is_fresh. Qed.
Hint Resolve fresh_stamp_spec : core.

Lemma ex_fresh_stamp {X} (g: gmap stamp X): { s | s ∉ gdom g }.
Proof. exists (fresh_stamp g). by apply fresh_stamp_spec. Qed.

Lemma insert_grow g s T: s ∉ gdom g → g ⊆ <[s:=T]> g.
Proof.
  intros Hfresh.
  apply insert_subseteq, (not_elem_of_dom (D := gset stamp)), Hfresh.
Qed.
Hint Resolve insert_grow : core.

Lemma ex_fresh_stamp_strong g T: { s | s ∉ gdom g ∧ g ⊆ <[s := T]> g }.
Proof.
  pose proof (ex_fresh_stamp g) as [s Hfresh].
  exists s; split; auto.
Qed.

Lemma ex_fresh_stamp_strong' g T: { s | s ∉ gdom g ∧ gdom g ⊆ gdom (<[s := T]> g) }.
Proof.
  pose proof (ex_fresh_stamp_strong g T) as [s []].
  exists s; split =>//=. by apply subseteq_dom.
Qed.

Lemma extraction_closed g n T s σ:
  T ~[ n ] (g, (s, σ)) →
  nclosed T n.
Proof. intros (T' & Hlook & <- & Hclσ & HclT'). apply: fv_to_subst; eauto. Qed.

Lemma extract_spec g n T: is_stamped_ty n g T → T ~[ n ] (extract g n T).
Proof.
  have Hle: g ⊆ <[fresh_stamp g := T]> g by eauto.
  exists T. rewrite lookup_insert closed_subst_idsρ ?length_idsσ;
  split_and?; eauto.
Qed.
Hint Resolve extract_spec : core.

Lemma extract_spec_rev g g' s σ n T:
  (g', (s, σ)) = (extract g n T) →
  T ~[ n ] (g', (s, σ)) → is_stamped_ty n g' T.
Proof.
  move => -[-> -> ->] [T']; rewrite length_idsσ lookup_insert => -[[->]]. int.
Qed.

Lemma extraction_inf_subst g n T s σ m σ':
  T ~[ n ] (g, (s, σ)) →
  is_stamped_sub n m g σ' →
  T.|[σ'] ~[ m ] (g, (s, σ.|[σ'])).
Proof.
  intros (T' & Hlook & <- & Hclσ & HclT') Hclσ' => /=. rewrite map_length.
  exists T'; split_and! => //.
  - asimpl. apply (is_stamped_nclosed_ty HclT'), to_subst_compose.
  - exact: is_stamped_sub_σ.
Qed.
Hint Resolve extraction_inf_subst : core.

Lemma extraction_subst g n T s σ m σ':
  T ~[ n ] (g, (s, σ)) →
  length σ' = n → is_stamped_σ m g σ' →
  T.|[∞ σ'] ~[ m ] (g, (s, σ.|[∞ σ'])).
Proof. intros; subst; eauto. Qed.
Hint Resolve extraction_subst : core.

Lemma extract_inf_subst_spec g g' n T s σ m σ':
  is_stamped_ty n g T →
  is_stamped_sub n m g' σ' →
  (g', (s, σ)) = extract g n T →
  T.|[σ'] ~[ m ] (g', (s, σ.|[σ'])).
Proof.
  intros * HclT Hclσ Heq.
  eapply extraction_inf_subst => //. rewrite Heq. auto.
Qed.
Local Hint Resolve extract_inf_subst_spec : core.

Lemma extract_subst_spec g g' n T s σ m σ':
  is_stamped_ty n g T →
  length σ' = n → is_stamped_σ m g' σ' →
  (g', (s, σ)) = extract g n T →
  T.|[∞ σ'] ~[ m ] (g', (s, σ.|[∞ σ'])).
Proof. intros; subst; eauto. Qed.
Hint Resolve extract_subst_spec : core.

Lemma extraction_mono T g g' s σ n:
  T ~[ n ] (g, (s, σ)) →
  g ⊆ g' →
  T ~[ n ] (g', (s, σ)).
Proof.
  cbn. intros (T' & Hlook & Heq & ? & ?) Hg.
  exists T'; split_and!; eauto. by eapply map_subseteq_spec.
Qed.
Hint Extern 5 (_ ~[ _ ] (_, _)) => try_once extraction_mono : core.

Lemma extract_spec_growg g n T g' sσ:
  (g', sσ) = extract g n T → g ⊆ g'.
Proof. move => [-> _]. apply insert_grow, fresh_stamp_spec. Qed.
Hint Resolve extract_spec_growg : core.

Lemma lookup_mono g g' s T:
  g !! s = Some T → g ⊆ g' →
  g' !! s = Some T.
Proof. move => Hlook /(_ s). rewrite Hlook /= => H. by case_match; subst. Qed.
Hint Extern 5 (_ !! _ = Some _) => try_once lookup_mono : core.

Lemma extract_lookup g g' s σ n T:
  (g', (s, σ)) = extract g n T → g' !! s = Some T.
Proof. move => [-> -> _]. by rewrite lookup_insert. Qed.
Hint Resolve extract_lookup : core.

Lemma extraction_lookup g s σ n T:
  T ~[ n ] (g, (s, σ)) → ∃ T', g !! s = Some T' ∧ T'.|[∞ σ] = T.
Proof. naive_solver. Qed.

Lemma extract_inf_subst_commute g g' g'' T ξ n m s1 σ1 s2 σ2:
  is_stamped_ty n g T →
  is_stamped_sub n m g' ξ →
  (g', (s1, σ1)) = extract g n T →
  (g'', (s2, σ2)) = extract g' m (T.|[ξ]) →
  T.|[ξ] ~[ m ] (g'', (s1, σ1.|[ξ])) ∧
  ∃ T1 T2,
    g'' !! s1 = Some T1 ∧
    g'' !! s2 = Some T2 ∧
    T1.|[∞ σ1.|[ξ]] = T2.|[∞ σ2].
Proof.
  rewrite /extract => HstT Hstξ Hext1 Hext2. split; first eauto.
  exists T, T.|[ξ]; split_and!; eauto.
  move: (is_stamped_nclosed_ty HstT) => HclT.
  move: (is_stamped_nclosed_sub Hstξ) => Hclξ.
  simplify_eq; rewrite (subst_compose _ _ HclT) //.
  rewrite !closed_subst_idsρ //. exact: nclosed_sub_app.
Qed.

Lemma extract_subst_commute g g' g'' T ξ n m s1 σ1 s2 σ2:
  is_stamped_ty n g T →
  is_stamped_σ m g' ξ →
  length ξ = n →
  (g', (s1, σ1)) = extract g n T →
  (g'', (s2, σ2)) = extract g' m (T.|[∞ ξ]) →
  T.|[∞ ξ] ~[ m ] (g'', (s1, σ1.|[∞ ξ])) ∧
  ∃ T1 T2,
    g'' !! s1 = Some T1 ∧
    g'' !! s2 = Some T2 ∧
    T1.|[∞ σ1.|[∞ ξ]] = T2.|[∞ σ2].
Proof. intros; subst; eapply extract_inf_subst_commute; eauto. Qed.
