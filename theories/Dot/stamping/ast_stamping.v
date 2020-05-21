(** Define "stamping" (what we used to call translation) in a purely syntactic
    way, without involving Iris. *)
From stdpp Require Import gmap.
From D Require Import tactics.
From D.Dot Require Import syn syn_lemmas type_extraction_syn core_stamping_defs
  skeleton unstampedness_binding lr_syn_aux.

Set Implicit Arguments.

Implicit Types
         (T: ty) (v: vl) (e: tm) (p: path) (d: dm) (ds: dms) (vs: vls)
         (Γ : ctx) (g: stys) (n: nat).

Lemma is_stamped_tm_skip i T g n e:
  is_stamped_tm i g e →
  is_stamped_tm i g (iterate tskip n e).
Proof. elim: n e => [//|n IHn] e Hs. constructor; exact: IHn. Qed.

(** Here we do not unstamp types from the map, and we can't: unstamping the map
    recursively might not be terminate. We need an unstamped map, which is
    what's produced in the first pass.
    However, this problem disappears because paths are just source variables, not values.
 *)
Definition unstamp_vstamp g vs s := (from_option dtysyn (dtysem vs s) (g !! s)).|[∞ vs].
Arguments unstamp_vstamp /.

Fixpoint unstamp_tm g (t: tm): tm :=
  match t with
  | tv v => tv (unstamp_vl g v)
  | tapp t1 t2 => tapp (unstamp_tm g t1) (unstamp_tm g t2)
  | tskip t => tskip (unstamp_tm g t)
  | tproj t l => tproj (unstamp_tm g t) l
  | tun u t => tun u (unstamp_tm g t)
  | tbin b t1 t2 => tbin b (unstamp_tm g t1) (unstamp_tm g t2)
  | tif t1 t2 t3 => tif (unstamp_tm g t1) (unstamp_tm g t2) (unstamp_tm g t3)
  end
with
unstamp_vl g (v: vl): vl :=
  match v with
  | vobj ds => vobj (map (mapsnd (unstamp_dm g)) ds)
  | vabs t => vabs (unstamp_tm g t)
  | vlit _ => v
  | var_vl _ => v
  end
with
unstamp_dm g (d: dm): dm :=
  match d with
  | dtysem vs s => unstamp_vstamp g vs s
  | dtysyn T => dtysyn (unstamp_ty g T)
  | dpt v => dpt (unstamp_path g v)
  end
with
unstamp_path g (p: path): path :=
  match p with
  | pv v => pv (unstamp_vl g v)
  | pself p l => pself (unstamp_path g p) l
  end
with
unstamp_ty g (T: ty): ty :=
  match T with
  | TTop => T
  | TBot => T
  | TAnd T1 T2 => TAnd (unstamp_ty g T1) (unstamp_ty g T2)
  | TOr T1 T2 => TOr (unstamp_ty g T1) (unstamp_ty g T2)
  | TLater T => TLater (unstamp_ty g T)
  | TAll T1 T2 => TAll (unstamp_ty g T1) (unstamp_ty g T2)
  | TMu T => TMu (unstamp_ty g T)
  | TTMem l T1 T2 => TTMem l (unstamp_ty g T1) (unstamp_ty g T2)
  | TVMem l T => TVMem l (unstamp_ty g T)
  | TSel p l => TSel (unstamp_path g p) l
  | TSing p => TSing (unstamp_path g p)
  | TPrim _ => T
  end.

Definition unstamp_dms g ds := map (mapsnd (unstamp_dm g)) ds.

Notation stamps_tm   n b e__u g e__s := (unstamp_tm   g e__s      = e__u      ∧ is_unstamped_tm   n b e__u ∧ is_stamped_tm   n g e__s).
Notation stamps_vl   n b v__u g v__s := (unstamp_vl   g v__s      = v__u      ∧ is_unstamped_vl   n b v__u ∧ is_stamped_vl   n g v__s).
Notation stamps_dm   n b d__u g d__s := (unstamp_dm   g d__s      = d__u      ∧ is_unstamped_dm   n b d__u ∧ is_stamped_dm   n g d__s).
Notation stamps_dms  n b d__u g d__s := (unstamp_dms  g d__s%list = d__u%list ∧ is_unstamped_dms  n b d__u ∧ is_stamped_dms  n g d__s).
Notation stamps_path n b p__u g p__s := (unstamp_path g p__s      = p__u      ∧ is_unstamped_path n b p__u ∧ is_stamped_path n g p__s).
Notation stamps_ty   n b T__u g T__s := (unstamp_ty   g T__s      = T__u%ty   ∧ is_unstamped_ty   n b T__u ∧ is_stamped_ty   n g T__s).

Definition unstamp_same_skel_tm_def e g : Prop := ∀ e_s,
  unstamp_tm   g e_s = e → same_skel_tm e e_s.
Definition unstamp_same_skel_vl_def v g : Prop := ∀ v_s,
  unstamp_vl   g v_s = v → same_skel_vl v v_s.
Definition unstamp_same_skel_dm_def d g : Prop := ∀ d_s,
  unstamp_dm   g d_s = d → same_skel_dm d d_s.
Definition unstamp_same_skel_path_def p g : Prop := ∀ p_s,
  unstamp_path g p_s = p → same_skel_path p p_s.
Definition unstamp_same_skel_ty_def T g : Prop := ∀ T_s,
  unstamp_ty   g T_s = T → same_skel_ty T T_s.

Lemma unstamp_same_skel_mut g :
  (∀ t, unstamp_same_skel_tm_def t g) ∧
  (∀ v, unstamp_same_skel_vl_def v g) ∧
  (∀ d, unstamp_same_skel_dm_def d g) ∧
  (∀ p, unstamp_same_skel_path_def p g) ∧
  (∀ T, unstamp_same_skel_ty_def T g).
Proof.
  apply syntax_mut_ind; intros ** E ?; destruct E;
    simplify_eq/=; intuition auto.
  - elim: l H => [//|[a d] ds IHds].
    rewrite Forall_cons /unstamp_same_skel_dm_def /= => -[Hd1 Hds1].
    split_and!; eauto. exact: IHds.
  - revert dependent g => g; by case: (g !! s).
Qed.

Lemma unstamp_same_skel_tm e e_s g: unstamp_tm g e_s = e → same_skel_tm e e_s.
Proof. apply unstamp_same_skel_mut. Qed.

Lemma unstamp_path2tm g p q :
  unstamp_path g p = q →
  unstamp_tm g (path2tm p) = path2tm q.
Proof. elim: p q => [v|p IHp l] [w|q l'] /= ?; simplify_eq; f_equal; auto. Qed.

(* Core cases of existence of translations. *)
Definition stamp_dtysyn g n T :=
  let '(g', (s, σ)) := (extract g n T) in
  (dtysem σ s, g').

Lemma unstamped_stamped_var n b g x :
  is_unstamped_vl n b (var_vl x) → is_stamped_vl n g (var_vl x).
Proof. inversion_clear 1; auto. Qed.

(** Unstamped types are already stamped, because they can't contain type
    definitions to stamp. *)
Lemma unstamped_stamped_path p g n:
  is_unstamped_path' n p → is_stamped_path n g p.
Proof.
  intros Hus; induction p; repeat with_is_unstamped ltac:(fun H => nosplit inverse H; clear H);
    naive_solver eauto using unstamped_stamped_var.
Qed.

Lemma unstamped_stamped_type T g n b:
  is_unstamped_ty n b T →
  is_stamped_ty n g T.
Proof.
  move: n. induction T => n Hus; inverse Hus; constructor;
    try by [|eapply IHT || eapply IHT1 || eapply IHT2; auto 2; auto with fv];
    exact: unstamped_stamped_path.
Qed.

Lemma unstamped_stamps_self_mut:
  (∀ t g n b, is_unstamped_tm   n b t → unstamp_tm g t = t) ∧
  (∀ v g n b, is_unstamped_vl   n b v → unstamp_vl g v = v) ∧
  (∀ d g n b, is_unstamped_dm   n b d → unstamp_dm g d = d) ∧
  (∀ p g n b, is_unstamped_path n b p → unstamp_path g p = p) ∧
  (∀ T g n b, is_unstamped_ty   n b T → unstamp_ty g T = T).
Proof.
  apply syntax_mut_ind; try by intros; with_is_unstamped inverse;
    simplify_eq/=; f_equal; eauto 2; by destruct (g !! s).
  elim => [//|[l d] ds /= IHds] IH g n b Hus. inverse IH.
  have [Hd Hds]: is_unstamped_dm (S n) b d ∧ is_unstamped_dms (S n) b ds.
  by inversion Hus as [ | | | ?? Hds]; simplify_eq/=; inverse Hds.
  einjection IHds => // *; repeat f_equal; eauto 2.
Qed.

Lemma unstamped_stamps_self_path g n b p: is_unstamped_path n b p →
  unstamp_path g p = p.
Proof. apply unstamped_stamps_self_mut. Qed.

Arguments extraction: simpl never.
Import traversals.Trav1.

Lemma stamp_dtysyn_spec {T n} g b:
  is_unstamped_dm n b (dtysyn T) →
  let '(g', (s, σ)) := (extract g n T) in
  let v' := (dtysem σ s) in
  stamps_dm n b (dtysyn T) g' v' ∧ g ⊆ g' ∧
    T ~[ n ] (g', (s, σ)).
Proof.
  intros Hus; inverse Hus.
  have Hext: T ~[ n ] (extract g n T)
    by apply /extract_spec /unstamped_stamped_type.
  destruct (extract g n T) as (g' & s & σ) eqn:Heq.
  rewrite /extract in Heq; simplify_eq.
  split_and!; try apply trav_dtysem with (T' := T) (ts' := (n, <[fresh_stamp g := T]> g));
    rewrite /= ?lookup_insert //= ?closed_subst_idsρ ?length_idsσ //;
    eauto using is_stamped_idsσ, unstamped_stamped_type.
Qed.

Lemma exists_stamped_dtysyn T n g b:
  is_unstamped_dm n b (dtysyn T) →
  { v' & { g' | stamps_dm n b (dtysyn T) g' v' ∧ g ⊆ g' } }.
Proof.
  intros Hus. destruct (stamp_dtysyn g n T) as (v', g') eqn:?. cbn in Heqp.
  have HclT: nclosed T n. by inverse Hus; eauto.
  edestruct (stamp_dtysyn_spec g Hus).
  exists v', g'; simplify_eq; eauto.
Qed.

Lemma var_stamps_to_self1 g x v: unstamp_vl g v = var_vl x → v = var_vl x.
Proof. by case: v. Qed.

Lemma path_stamps_to_self1 g p_s p_u x: unstamp_path g p_s = p_u → path_root p_u = var_vl x → p_s = p_u.
Proof.
  elim: p_s p_u => /= [v_s|p_s IHp l] [] *;
    simplify_eq/=; f_equal; eauto using var_stamps_to_self1.
Qed.

Lemma unstamp_dms_hasnt ds ds' l g: dms_hasnt ds l → unstamp_dms g ds' = ds → dms_hasnt ds' l.
Proof.
  rewrite /dms_hasnt; elim: ds ds' => [| [s d] ds IH] [|[s' d'] ds'] // *.
  by simplify_eq/=; case_match; eauto.
Qed.

Lemma stamps_tm_skip n g i e e' b:
  stamps_tm n b e g e' →
  stamps_tm n b (iterate tskip i e) g (iterate tskip i e').
Proof.
  move => [Heq [Hus Hs]]. elim: i => [//|] i [IHeq [IHus IHs]].
  rewrite !iterate_S /=. split_and!; by [constructor| f_equiv].
Qed.
Hint Resolve stamps_tm_skip : core.

Lemma exists_stamped_dtysem vs s n g b: is_unstamped_dm n b (dtysem vs s) → { v' & { g' | stamps_dm n b (dtysem vs s) g' v' ∧ g ⊆ g' } }.
Proof. intros H. exfalso. by inversion H. Qed.

Lemma stamps_unstamp_dtysem_mono g1 g2 n v__u vs s b:
  g1 ⊆ g2 →
  stamps_dm n b v__u g1 (dtysem vs s) →
  unstamp_dm g2 (dtysem vs s) = v__u.
Proof.
  intros Hg (Huns & _ & Hs).
  assert (∃ T, g1 !! s = Some T) as [T__s Hlook1]. by inverse Hs; cbn in *; ev; econstructor.
  assert (g2 !! s = Some T__s) as Hlook2. by eapply map_subseteq_spec.
  move: Huns. by rewrite /= Hlook1 Hlook2.
Qed.

Lemma Forall2_eq_to_eqmap g2 (ds__s ds__u: dms) :
  Forall2 (λ d__s d__u, mapsnd (unstamp_dm g2) d__s = d__u) ds__s ds__u →
  map (mapsnd (unstamp_dm g2)) ds__s = ds__u.
Proof.
  elim: ds__s ds__u => [|[l d] /= ds IHds] ds__u Hf; inverse Hf => //=.
  f_equal. exact: IHds.
Qed.

Lemma stamps_unstamp_mono_mut:
  (∀ e__s g1 g2 n e__u b, g1 ⊆ g2 →
                    stamps_tm n b e__u g1 e__s →
                    unstamp_tm g2 e__s = e__u) ∧
  (∀ v__s g1 g2 n v__u b, g1 ⊆ g2 →
                    stamps_vl n b v__u g1 v__s →
                    unstamp_vl g2 v__s = v__u) ∧
  (∀ d__s g1 g2 n d__u b, g1 ⊆ g2 →
                    stamps_dm n b d__u g1 d__s →
                    unstamp_dm g2 d__s = d__u) ∧
  (∀ p__s g1 g2 n p__u b, g1 ⊆ g2 →
                    stamps_path n b p__u g1 p__s →
                    unstamp_path g2 p__s = p__u) ∧
  (∀ T__s g1 g2 n T__u b, g1 ⊆ g2 →
                    stamps_ty n b T__u g1 T__s →
                    unstamp_ty g2 T__s = T__u).
Proof.
  apply syntax_mut_ind; intros; ev; try (exact: stamps_unstamp_dtysem_mono);
    with_is_stamped inverse; with_is_unstamped inverse;
    try naive_solver eauto with f_equal.
  f_equal/=; apply Forall2_eq_to_eqmap.
  generalize dependent ds => ds; rewrite !Forall_fmap; intros; decompose_Forall.
  generalize dependent x => -[l1 d1] /= Hl1 Hus1 Hs1 IH.
  generalize dependent y => -[l2 d2]; rewrite list_lookup_fmap Hl1 /=.
  naive_solver eauto with f_equal.
Qed.

Lemma stamps_unstamp_mono_tm e__s g1 g2 n e__u b: g1 ⊆ g2 →
                                    stamps_tm n b e__u g1 e__s →
                                    unstamp_tm g2 e__s = e__u.
Proof. apply stamps_unstamp_mono_mut. Qed.
Lemma stamps_unstamp_mono_vl v__s g1 g2 n v__u  b: g1 ⊆ g2 →
                                  stamps_vl n b v__u g1 v__s →
                                  unstamp_vl g2 v__s = v__u.
Proof. apply stamps_unstamp_mono_mut. Qed.
Lemma stamps_unstamp_mono_dm d__s g1 g2 n d__u b: g1 ⊆ g2 →
                                    stamps_dm n b d__u g1 d__s →
                                    unstamp_dm g2 d__s = d__u.
Proof. apply stamps_unstamp_mono_mut. Qed.
Lemma stamps_unstamp_mono_path p__s g1 g2 n p__u b: g1 ⊆ g2 →
                                    stamps_path n b p__u g1 p__s →
                                    unstamp_path g2 p__s = p__u.
Proof. apply stamps_unstamp_mono_mut. Qed.
Lemma stamps_unstamp_mono_ty T__s g1 g2 n T__u b: g1 ⊆ g2 →
                                  stamps_ty n b T__u g1 T__s →
                                  unstamp_ty g2 T__s = T__u.
Proof. apply stamps_unstamp_mono_mut. Qed.
