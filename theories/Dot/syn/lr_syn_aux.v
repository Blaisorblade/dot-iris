(**
Syntactic predicates used to define our logical relation for DOT,
and misc. useful lemmas.
*)
From D Require Export prelude.
From iris.program_logic Require Import language.
From D.Dot Require Export syn rules.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (p : path)
         (Γ : ctx) (ρ : env) (Pv : vl → Prop).

Unset Program Cases.

Lemma tskip_subst i e s: (iterate tskip i e).|[s] = iterate tskip i e.|[s].
Proof. exact: cons_subst. Qed.

Lemma TLater_subst i T s: (iterate TLater i T).|[s] = iterate TLater i T.|[s].
Proof. exact: cons_subst. Qed.

Lemma path2tm_subst p ρ: (path2tm p).|[ρ] = path2tm p.|[ρ].
Proof. by elim: p => /= [//|p -> l]. Qed.

(******************************************************************************)
(** [path_wp], but for Coq predicates. *)
(******************************************************************************)

Inductive path_wp_pure : path → (vl → Prop) → Prop :=
| pwp_pv vp Pv : Pv vp → path_wp_pure (pv vp) Pv
| pwp_pself p vp q l Pv : path_wp_pure p (eq vp) → vp @ l ↘ dpt q → path_wp_pure q Pv →
  path_wp_pure (pself p l) Pv .
Local Hint Constructors path_wp_pure : core.

Lemma path_wp_pure_pv_eq Pv v : path_wp_pure (pv v) Pv ↔ Pv v.
Proof. split; by [inversion_clear 1 | auto]. Qed.

Lemma path_wp_pure_pself_eq Pv p l : path_wp_pure (pself p l) Pv →
  ∃ vp q, path_wp_pure p (eq vp) ∧ vp @ l ↘ dpt q ∧ path_wp_pure q Pv ∧
  path_wp_pure (pself p l) Pv.
Proof. inversion_clear 1; naive_solver. Qed.

Global Instance Proper_pwp_pure: Proper ((=) ==> pointwise_relation _ iff ==> iff) path_wp_pure.
Proof.
  (* The induction works best in this shape, but this instance is best kept local. *)
  have Proper_pwp_2: ∀ p, Proper (pointwise_relation _ iff ==> iff) (path_wp_pure p).
  by rewrite /pointwise_relation => p P1 P2 HPeq; split;
    induction 1; naive_solver.
  solve_proper.
Qed.

Lemma path_wp_pure_wand {Pv1 Pv2 p}:
  path_wp_pure p Pv1 →
  (∀ v, Pv1 v → Pv2 v) →
  path_wp_pure p Pv2.
Proof. elim; eauto. Qed.

Lemma path_wp_pure_eq p Pv :
  path_wp_pure p Pv ↔ ∃ v, path_wp_pure p (eq v) ∧ Pv v.
Proof.
  split.
  - elim; naive_solver.
  - move => [v [Hpeq HPv]]. dependent induction Hpeq; naive_solver.
Qed.

Lemma path_wp_pure_det {p v1 v2}:
  path_wp_pure p (eq v1) →
  path_wp_pure p (eq v2) →
  v1 = v2.
Proof.
  move => Hp1 Hp2; move: v2 Hp2; induction Hp1; intros; inverse Hp2; first naive_solver.
  lazymatch goal with H1 : ?vp @ l ↘ dpt ?q, H2 : ?vp0 @ l ↘ dpt ?q0 |- _ =>
    (suff ?: q = q0 by subst; auto);
    (suff ?: vp = vp0 by subst; objLookupDet);
    auto
  end.
Qed.

Lemma path_wp_pure_swap p w :
  path_wp_pure p (λ v, v = w) ↔
  path_wp_pure p (eq w).
Proof. split => Hp; exact: path_wp_pure_wand. Qed.

Lemma path_wp_exec_pure p v :
  path_wp_pure p (eq v) →
  ∃ n, PureExec True n (path2tm p) (tv v).
Proof.
  move HE: (eq v) => P Hp; move: v HE; induction Hp; intros; simplify_eq.
  by exists 0; constructor.
  have [m /(_ I) Hs1] := IHHp1 _ eq_refl.
  have [n /(_ I) Hs2] := IHHp2 _ eq_refl.
  exists (S m + n) => _ /=.
  eapply (nsteps_trans (S m)), Hs2; eapply nsteps_r.
  by apply (pure_step_nsteps_ctx (fill_item (ProjCtx l))), Hs1.
  by apply nsteps_once_inv, pure_tproj.
Qed.

Lemma PureExec_to_terminates n φ e v : PureExec φ n e (tv v) → φ → terminates e.
Proof. intros HP Hφ. exists v. eapply nsteps_rtc, HP, Hφ. Qed.

Definition alias_paths p q :=
  path_wp_pure q (λ vp, path_wp_pure p (eq vp)).

Lemma alias_paths_pv_eq_1 p vr :
  alias_paths p (pv vr) ↔ path_wp_pure p (eq vr).
Proof. rewrite /alias_paths. by setoid_rewrite path_wp_pure_pv_eq. Qed.

Hint Extern 1 (path_wp_pure _ _) => by apply path_wp_pure_swap : core.

Lemma alias_paths_pv_eq_2 p vr :
  alias_paths (pv vr) p ↔ path_wp_pure p (eq vr).
Proof.
  rewrite /alias_paths -path_wp_pure_swap.
  by setoid_rewrite path_wp_pure_pv_eq.
Qed.

Lemma alias_paths_self p v :
  alias_paths p (pv v) → alias_paths p p.
Proof.
  rewrite alias_paths_pv_eq_1 /alias_paths !path_wp_pure_eq; naive_solver.
Qed.

Lemma alias_paths_refl_vl v :
  alias_paths (pv v) (pv v).
Proof. hnf; eauto. Qed.

Lemma alias_paths_sameres p q:
  alias_paths p q ↔
  ∃ v,
    path_wp_pure p (eq v) ∧
    path_wp_pure q (eq v).
Proof. rewrite /alias_paths !path_wp_pure_eq; naive_solver. Qed.

Lemma alias_paths_symm p q :
  alias_paths p q ↔ alias_paths q p.
Proof. rewrite !alias_paths_sameres. naive_solver. Qed.
Lemma alias_paths_symm' p q :
  alias_paths p q → alias_paths q p.
Proof. apply alias_paths_symm. Qed.

Lemma alias_paths_trans p q r :
  alias_paths p q → alias_paths q r → alias_paths p r.
Proof.
  rewrite !alias_paths_sameres => -[v [Hpv Hqv]] [w [Hqw Hrw]].
  have Heq: v = w by exact: path_wp_pure_det. simplify_eq; eauto.
Qed.

Lemma alias_paths_samepwp_pure p q:
  alias_paths p q ↔
    (∃ u, path_wp_pure p (eq u)) ∧
    ∀ Pv, path_wp_pure p Pv ↔ path_wp_pure q Pv.
Proof.
  rewrite alias_paths_sameres; split.
  - destruct 1 as (v & Hp & Hq).
    split. by eauto. intros Pv.
    rewrite !path_wp_pure_eq.
    f_equiv => w; split => -[Hr];
      [ rewrite -(path_wp_pure_det Hp Hr)
      | rewrite -(path_wp_pure_det Hq Hr)]; auto.
  - intros [[u Hp] Heq]. exists u.
    split; by [|rewrite -Heq].
Qed.

Lemma alias_paths_elim_eq_pure Pv {p q}:
  alias_paths p q →
  path_wp_pure p Pv ↔ path_wp_pure q Pv.
Proof. move => /alias_paths_samepwp_pure [_]. apply. Qed.

Lemma alias_paths_pself {p q l w} :
  path_wp_pure (pself q l) (eq w) →
  alias_paths p q →
  alias_paths (pself p l) (pself q l).
Proof.
  intros Hql Hal; inverse Hql; econstructor; eauto.
  rewrite path_wp_pure_eq; exists w; split => //; econstructor; eauto.
  by rewrite (alias_paths_elim_eq_pure _ Hal).
Qed.

Lemma alias_paths_simpl {p q} :
  path_wp_pure p (λ v, alias_paths q (pv v)) ↔
  alias_paths p q.
Proof. setoid_rewrite alias_paths_pv_eq_1. apply alias_paths_symm. Qed.

(******************************************************************************)
(** For primitives. *)
(******************************************************************************)
Definition prim_sem (B : base_ty) :=
  match B with
  | tbool => bool
  | tnat => nat
  end.

Definition prim_evals_to (B : base_ty) (v : vl) : prim_sem B → Prop :=
  match B return prim_sem B → Prop with
  | tbool => λ l, v = vlit $ lbool l
  | tnat  => λ l, v = vlit $ lnat l
  end.

Definition pure_interp_prim B v := ∃ l : prim_sem B, prim_evals_to B v l.

(******************************************************************************)
(** For definition typing. *)
(******************************************************************************)

Definition label_of_ty T : option label :=
  match T with
  | TTMem l _ _ => Some l
  | TVMem l _ => Some l
  | _ => None
  end.

(** Context extension for use with definition typing, as in
    [Γ |L V ⊨d d : T] and [Γ |L V ⊨ds ds : T]. *)
Definition defCtxCons Γ V := TLater V :: Γ.
Notation "Γ |L V" := (defCtxCons Γ V) (at level 60).

Lemma norm_selfSubst ds s: selfSubst ds.|[up s] = ds.|[(vobj ds).[s] .: s].
Proof. by rewrite /selfSubst up_sub_compose. Qed.

(** Presence and absence of definitions. *)
Definition dms_has ds l d := dms_lookup l ds = Some d.
Definition dms_hasnt ds l := dms_lookup l ds = None.

Lemma dms_hasnt_map ds l f:
  dms_hasnt ds l →
  dms_hasnt (map (mapsnd f) ds) l.
Proof.
  elim: ds => //; rewrite /dms_hasnt/mapsnd/= => [[l' d] ds IHds H].
  by case_decide; eauto 2.
Qed.

Lemma dms_hasnt_subst l ds ρ : dms_hasnt ds l → dms_hasnt ds.|[ρ] l.
Proof. apply dms_hasnt_map. Qed.

Lemma dms_lookup_head l d ds: dms_lookup l ((l, d) :: ds) = Some d.
Proof. by cbn; case_decide. Qed.

Lemma dms_lookup_mono l l' d d' ds:
  dms_hasnt ds l →
  dms_lookup l' ds = Some d' →
  dms_lookup l' ((l, d) :: ds) = Some d'.
Proof.
  rewrite /dms_hasnt /= => Hlds Hl; by case_decide; simplify_eq.
Qed.

Lemma dms_hasnt_notin_eq l ds : dms_hasnt ds l ↔ l ∉ map fst ds.
Proof.
  elim: ds => [|[l' d] ds] /=; first by split; [inversion 2|].
  rewrite /dms_hasnt/= not_elem_of_cons => IHds. case_decide; naive_solver.
Qed.

(** Well-formedness of definition lists. *)
Notation wf_ds ds := (NoDup (map fst ds)).

(** Definitions [ds] appear in the object resulting from evaluating path [ p.|[ρ] ]. *)
Definition path_includes p ρ ds :=
  path_wp_pure p.|[ρ] (λ w, ∃ ds', w = vobj ds' ∧ ds.|[ρ] `sublist_of` selfSubst ds' ∧ wf_ds ds').

Lemma ds_notin_subst l ds ρ :
  l ∉ map fst ds →
  l ∉ map fst ds.|[ρ].
Proof.
  (* elim: ds => [//|[l' d] ds IH]; cbn.
  rewrite !not_elem_of_cons. naive_solver. *)
  intros; by apply dms_hasnt_notin_eq, dms_hasnt_subst, dms_hasnt_notin_eq.
Qed.

Lemma wf_ds_nil : wf_ds ([] : dms). Proof. constructor. Qed.
Hint Resolve wf_ds_nil : core.

Lemma wf_ds_sub ds ρ : wf_ds ds → wf_ds ds.|[ρ].
Proof.
  elim: ds => [//=|[l d] ds IH]; cbn.
  inversion_clear 1; constructor; last by eauto.
  exact: ds_notin_subst.
Qed.

Lemma path_includes_self ds ρ : wf_ds ds → path_includes (pv (ids 0)) (vobj ds.|[up ρ] .: ρ) ds.
Proof.
  by constructor; exists ds.|[up ρ]; rewrite /= /selfSubst up_sub_compose; split_and!;
    last apply wf_ds_sub.
Qed.

Lemma path_includes_split p ρ l d ds :
  path_includes p ρ ((l, d) :: ds) →
  path_includes p ρ [(l, d)] ∧
  path_includes p ρ ds.
Proof.
  rewrite /path_includes !path_wp_pure_eq; cbn.
  intros (v & Hpw & ds' & -> & ((k1 & k2 & Hpid & Hpids)%sublist_cons_l & Hno)).
  repeat (split_and! => //; try eexists); rewrite Hpid; apply sublist_inserts_l.
  by apply sublist_skip, sublist_nil_l.
  by apply sublist_cons, Hpids.
Qed.

Lemma dms_has_in_eq l d ds : wf_ds ds →
  dms_has ds l d ↔ (l, d) ∈ ds.
Proof.
  rewrite /dms_has; elim: ds => [Hwf|[l' d'] ds IH /= /NoDup_cons [Hni Hwf]];
    [by split; [|inversion 1]| rewrite elem_of_cons].
  case_decide; first split; first 1 last; [|naive_solver..].
  destruct 1; simplify_eq/=; [naive_solver|destruct Hni].
  by eapply elem_of_list_In, (in_map fst ds (_,_)), elem_of_list_In.
Qed.

Lemma dms_lookup_sublist l p ds :
  wf_ds ds → [(l, dpt p)] `sublist_of` ds →
  dms_lookup l ds = Some (dpt p).
Proof.
  rewrite sublist_cons_l; intros Hwf ?; ev; simplify_eq/=.
  apply dms_has_in_eq; [done|].
  rewrite elem_of_app elem_of_cons. naive_solver.
Qed.

Lemma path_includes_field_aliases p ρ l v :
  path_includes p ρ [(l, dpt (pv v))] →
  alias_paths (pself p.|[ρ] l) (pv v.[ρ]).
Proof.
  rewrite /path_includes/alias_paths/= !path_wp_pure_eq;
    intros (w & Hwp & ds & -> & Hsub & Hwf').
  enough (dms_lookup l (selfSubst ds) = Some (dpt (pv v.[ρ]))) by eauto 10.
  apply dms_lookup_sublist, Hsub. exact: wf_ds_sub.
Qed.
