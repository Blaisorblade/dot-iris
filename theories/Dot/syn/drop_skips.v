(** * Show simulation between terms and skip-free terms.
Ideally we would want a bisimulation, so this is incomplete, but left as
future work in the paper. *)
From iris.program_logic Require Import language ectx_language ectxi_language.
From D Require Import prelude.
From D.Dot Require Import syn.

Implicit Types
         (T : ty) (v : vl) (e t : tm) (d : dm) (ds : dms) (p : path)
         (Γ : ctx) (vs : vls) (l : label).

Program Fixpoint erase_tm e :=
  match e with
  | tv v => tv (erase_vl v)
  | tapp e1 e2 => tapp (erase_tm e1) (erase_tm e2)
  | tskip e => erase_tm e
  | tproj e l => tproj (erase_tm e) l
  | tun u e => tun u (erase_tm e)
  | tbin b e1 e2 => tbin b (erase_tm e1) (erase_tm e2)
  | tif e1 e2 e3 => tif (erase_tm e1) (erase_tm e2) (erase_tm e3)
  end
with erase_vl v :=
  match v with
  | vobj ds => vobj (map (mapsnd erase_dm) ds)
  | vabs e => vabs (erase_tm e)
  | var_vl _ => v
  | vlit _ => v
  end
with erase_dm d :=
  match d with
  | dpt p => dpt (erase_pt p)
  | dtysyn T => dtysyn (erase_ty T)
  | dtysem σ s => dtysem (map erase_vl σ) s
  end
with erase_pt p :=
  match p with
  | pv v => pv (erase_vl v)
  | pself p l => pself (erase_pt p) l
  end
with erase_ty T :=
  match T with
  | TTop => T
  | TBot => T
  | TAnd T1 T2 => TAnd (erase_ty T1) (erase_ty T2)
  | TOr T1 T2 => TOr (erase_ty T1) (erase_ty T2)
  | TLater T => TLater (erase_ty T)
  | TAll T1 T2 => TAll (erase_ty T1) (erase_ty T2)
  | TMu T => TMu (erase_ty T)
  | TVMem l T => TVMem l (erase_ty T)
  | TTMem l T1 T2 => TTMem l (erase_ty T1) (erase_ty T2)
  | TSel p l => TSel (erase_pt p) l
  | TPrim b => T
  | TSing p => TSing (erase_pt p)
  end.

Notation erase_dms := (map (mapsnd erase_dm)).
Notation erase_σ := (map erase_vl).
Definition erase_ρ (ρ : var → vl) : var → vl := ρ >>> erase_vl.

Lemma erase_scons v : erase_ρ (v .: ids) = erase_vl v .: ids.
Proof. by f_ext => -[|n]. Qed.

Definition erase_vl_rename_def v := ∀ ξ, erase_vl (v.[ren ξ]) = (erase_vl v).[ren ξ].
Definition erase_tm_rename_def e := ∀ ξ, erase_tm (e.|[ren ξ]) = (erase_tm e).|[ren ξ].
Definition erase_dm_rename_def d := ∀ ξ, erase_dm (d.|[ren ξ]) = (erase_dm d).|[ren ξ].
Definition erase_pt_rename_def p := ∀ ξ, erase_pt (p.|[ren ξ]) = (erase_pt p).|[ren ξ].
Definition erase_ty_rename_def T := ∀ ξ, erase_ty (T.|[ren ξ]) = (erase_ty T).|[ren ξ].

Lemma erase_rename_mut :
  (∀ t, erase_tm_rename_def t) ∧ (∀ v, erase_vl_rename_def v) ∧
  (∀ d, erase_dm_rename_def d) ∧ (∀ p, erase_pt_rename_def p) ∧
  (∀ T, erase_ty_rename_def T).
Proof.
  apply syntax_mut_ind; repeat intro; simpl in *; f_equal;
    rewrite ?up_upren_vl; auto;
    [generalize dependent ds | generalize dependent vs];
    elim => [//|x xs IHxs] Hxs'; ev; cbn; inversion Hxs' as [|?? Hx Hxs];
    auto with f_equal.
Qed.

Lemma erase_subst_up ρ : erase_ρ (up ρ) = up (erase_ρ ρ).
Proof. f_ext => -[//|n]; asimpl. apply erase_rename_mut. Qed.

Definition erase_vl_subst_def v := ∀ ρ, erase_vl (v.[ρ]) = (erase_vl v).[erase_ρ ρ].
Definition erase_tm_subst_def e := ∀ ρ, erase_tm (e.|[ρ]) = (erase_tm e).|[erase_ρ ρ].
Definition erase_dm_subst_def d := ∀ ρ, erase_dm (d.|[ρ]) = (erase_dm d).|[erase_ρ ρ].
Definition erase_pt_subst_def p := ∀ ρ, erase_pt (p.|[ρ]) = (erase_pt p).|[erase_ρ ρ].
Definition erase_ty_subst_def T := ∀ ρ, erase_ty (T.|[ρ]) = (erase_ty T).|[erase_ρ ρ].

Lemma erase_subst_mut :
  (∀ t, erase_tm_subst_def t) ∧ (∀ v, erase_vl_subst_def v) ∧
  (∀ d, erase_dm_subst_def d) ∧ (∀ p, erase_pt_subst_def p) ∧
  (∀ T, erase_ty_subst_def T).
Proof.
  apply syntax_mut_ind; repeat intro; simpl in *; f_equal;
    rewrite -?erase_subst_up; auto;
    [generalize dependent ds | generalize dependent vs];
    elim => [//|x xs IHxs] Hxs'; ev; cbn; inversion Hxs' as [|?? Hx Hxs];
    auto with f_equal.
Qed.

Lemma erase_tm_subst : ∀ e, erase_tm_subst_def e.
Proof. apply erase_subst_mut. Qed.
Lemma erase_dm_subst : ∀ d, erase_dm_subst_def d.
Proof. apply erase_subst_mut. Qed.

Lemma erase_dms_subst ds ρ : erase_dms ds.|[ρ] = (erase_dms ds).|[erase_ρ ρ].
Proof. elim: ds => [//|[l d] ds IHds]; cbn. by rewrite erase_dm_subst IHds. Qed.

(** For beta-reduction *)
Lemma erase_tm_subst_beta e1 v2 :
  erase_tm e1.|[v2/] = (erase_tm e1).|[erase_vl v2/].
Proof. by rewrite erase_tm_subst erase_scons. Qed.

(** For field projections. *)
Lemma erase_tm_path2tm p : erase_tm (path2tm p) = path2tm (erase_pt p).
Proof. elim: p => [v|p /= IHp l] //. by f_equal. Qed.

Lemma erase_selfSubst ds : selfSubst (erase_dms ds) = erase_dms (selfSubst ds).
Proof. by rewrite erase_dms_subst erase_scons. Qed.

Lemma erase_dms_index_gen ds p l :
  dms_lookup l ds = Some (dpt p) →
  dms_lookup l (erase_dms ds) = Some (dpt (erase_pt p)).
Proof.
  elim: ds => [//|[l' d] ds IHds]; cbn => Hl.
  case_decide; simplify_eq/=; eauto.
Qed.

Lemma erase_objLookup v l p :
  v @ l ↘ dpt p → erase_vl v @ l ↘ dpt (erase_pt p).
Proof.
  move => [ds [-> Hl]]/=. exists (erase_dms ds); split_and! => //.
  rewrite erase_selfSubst. exact: erase_dms_index_gen.
Qed.

(** For primitive operations. *)
Lemma erase_un_op_eval u v1 w:
  un_op_eval u v1 = Some w →
  un_op_eval u (erase_vl v1) = Some (erase_vl w).
Proof. intros; destruct u, v1 => //=; case_match; naive_solver. Qed.

Lemma erase_bin_op_eval b v1 v2 w:
  bin_op_eval b v1 v2 = Some w →
  bin_op_eval b (erase_vl v1) (erase_vl v2) = Some (erase_vl w).
Proof.
  intros; destruct v1 => //=; destruct v2 => //=; simplify_eq/=;
    repeat (case_match; try done); simplify_eq/=;
    destruct b; simplify_eq/=; try case_decide; try case_match; try naive_solver.
Qed.

Lemma head_erase_sim e1 e2 :
  head_step e1 () [] e2 () [] →
  rtc (λ e1 e2, head_step e1 () [] e2 () []) (erase_tm e1) (erase_tm e2).
Proof.
  intros Hs; dependent induction Hs; simplify_eq/=;
    first [exact: rtc_refl | apply rtc_once]; try by constructor.
  - rewrite erase_tm_subst_beta; exact: st_beta.
  - rewrite erase_tm_path2tm; by apply st_proj, erase_objLookup.
  - by apply st_un, erase_un_op_eval.
  - by apply st_bin, erase_bin_op_eval.
Qed.

Definition erase_ctxi (K : ectx_item) : list ectx_item :=
  match K with
  | AppLCtx e2 => [AppLCtx $ erase_tm e2]
  | AppRCtx v1 => [AppRCtx $ erase_vl v1]
  | ProjCtx l => [K]
  | SkipCtx => []
  | UnCtx u => [K]
  | BinLCtx b e2 => [BinLCtx b $ erase_tm e2]
  | BinRCtx b v1 => [BinRCtx b $ erase_vl v1]
  | IfCtx e1 e2 => [IfCtx (erase_tm e1) (erase_tm e2)]
  end.

Lemma erase_ctxi_fill_item (K : ectx_item) e :
  erase_tm (fill_item K e) = fill (erase_ctxi K) (erase_tm e).
Proof. by induction K. Qed.

Definition erase_ctxi_list := mbind erase_ctxi.
Lemma erase_ctxi_fill (Ks : list ectx_item) e :
  erase_tm (fill Ks e) = fill (erase_ctxi_list Ks) (erase_tm e).
Proof.
  elim: Ks e => [//|K Ks IH] e. by rewrite /= fill_app IH erase_ctxi_fill_item.
Qed.

Lemma erase_ectx_app K K' : erase_ctxi_list (K ++ K') = erase_ctxi_list K ++ erase_ctxi_list K'.
Proof. by rewrite /erase_ctxi_list bind_app. Qed.

(* Good proof, but unused *)
(* Lemma erase_ectx_tm K e :
  erase_tm (fill K e) = fill (erase_ctxi_list K) (erase_tm e).
Proof.
  move: e; induction K as [|Ki K IHK] using rev_ind; simplify_eq/=; first done.
  move=> e.
  rewrite !erase_ectx_app !fill_app /= -IHK {IHK}.
  induction Ki; rewrite /= ?fill_app /=; eauto with f_equal.
Qed. *)

Definition simpl_prim_step := (λ e1 e2, prim_step e1 () [] e2 () []).
Notation prim_steps := (rtc simpl_prim_step).

Theorem simulation_skiperase e1 e2 :
  simpl_prim_step e1 e2 →
  prim_steps (erase_tm e1) (erase_tm e2).
Proof.
  inversion 1 as [Ks ???? Hh%head_erase_sim]; simplify_eq/=.
  rewrite !erase_ctxi_fill. induction Hh; [apply rtc_refl|eapply rtc_l, IHHh].
  by econstructor.
Qed.

(* Reuse lemmas relating Iris's various wrappers of reduction relations. *)
From D.Dot Require Import skeleton.
From D Require Import iris_extra.det_reduction.

Lemma simulation_skiperase' e1 σ1 κ e2 σ2 efs :
  prim_step e1 σ1 κ e2 σ2 efs →
  prim_steps (erase_tm e1) (erase_tm e2).
Proof.
  intros Hs; prim_step_inversion Hs.
  destruct σ1; exact: simulation_skiperase.
Qed.
Lemma erased_step_inversion {t1 thp σ σ'} :
  erased_step ([t1], σ) (thp, σ') →
  ∃ t2, thp = [t2] ∧ prim_step t1 σ [] t2 σ' [].
Proof. move => [? /step_inversion H]; naive_solver. Qed.

Lemma rtc_erased_step_inversion' {t1 thp σ σ'} :
  rtc erased_step ([t1], σ) (thp, σ') →
  ∃ t2, thp = [t2].
Proof.
  intros Hs; dependent induction Hs. naive_solver.
  hnf in *; ev; edestruct @erased_step_inversion; first hnf in *;
  naive_solver eauto using erased_step_inversion.
Qed.

Theorem rtc_erased_step_inversion {t1 t2 σ σ' thp} :
  rtc erased_step ([t1], σ) (thp, σ') → t2 ∈ thp →
  rtc erased_step ([t1], σ) ([t2], σ').
Proof.
  move=> Hs; have [t2' ?] := rtc_erased_step_inversion' Hs; subst.
  by rewrite elem_of_list_singleton=>->.
Qed.

Lemma erased_prim_steps e1 e2:
  rtc erased_step ([e1], ()) ([e2], ()) ↔
  prim_steps e1 e2.
Proof.
  split; intros Hs; dependent induction Hs => //.
  - destruct y as [? []].
    edestruct @erased_step_inversion as [e'] => //; ev; simplify_eq.
    trans e'; by [exact: rtc_once|auto].
  - trans ([y], ()) => //. apply rtc_once.
    exists []; eauto.
Qed.

Theorem simulation_skip_erase_prim_steps t1 t2 :
  prim_steps t1 t2 →
  prim_steps (erase_tm t1) (erase_tm t2).
Proof.
  intros Hsteps; dependent induction Hsteps; first done.
  etrans; last done.
  exact: simulation_skiperase'.
Qed.

Theorem simulation_skiperase_erased_steps {t1 t2 σ σ'} :
  rtc erased_step ([t1], σ) ([t2], σ') →
  rtc erased_step ([erase_tm t1], σ) ([erase_tm t2], σ').
Proof.
  uniqueState; rewrite !erased_prim_steps.
  exact: simulation_skip_erase_prim_steps.
Qed.

Corollary simulation_skiperase_erased_steps_vl {t1 v2 σ σ'} :
  rtc erased_step ([t1], σ) ([tv v2], σ') →
  rtc erased_step ([erase_tm t1], σ) ([tv (erase_vl v2)], σ').
Proof. exact: (simulation_skiperase_erased_steps (t2 := tv v2)). Qed.


Lemma fill_prim_steps Ks {eK1 eK2} :
  prim_steps eK1 eK2 →
  prim_steps (fill Ks eK1) (fill Ks eK2).
Proof. intros Hs; eapply rtc_congruence, Hs; intros; exact: fill_prim_step. Qed.

Lemma prim_steps_tskip_congruence {e1 e2}:
  prim_steps e1 e2 → prim_steps (tskip e1) (tskip e2).
Proof. exact: (fill_prim_steps [SkipCtx]). Qed.

Lemma tskip_preserves_termination e v:
  prim_steps e (tv v) → prim_steps (tskip e) (tv v).
Proof.
  intros Hs; eapply rtc_transitive with (y := tskip (tv v));
    last by apply rtc_once, head_prim_step, st_skip.
  exact: prim_steps_tskip_congruence.
Qed.

Lemma unerased_value_steps_to_value e v :
  tv v = erase_tm e →
  ∃ v', prim_steps e (tv v') ∧ erase_vl v' = v.
Proof.
  elim: e v => [v| | |e IHe| | | ] w He *; simplify_eq/=; first naive_solver.
  destruct (IHe w He) as [v [Hs <-]]. exists v; split_and!; last done.
  exact: tskip_preserves_termination.
Qed.

Definition prim_steps_to_erasure_of e1 e2 :=
  ∃ e2', prim_steps e1 e2' ∧ erase_tm e2' = e2.

From D.Dot.syn Require Import path_repl.

Lemma prim_steps_tapp_congruence1 {t1 t2 u}:
  prim_steps t1 t2 →
  prim_steps (tapp t1 u) (tapp t2 u).
Proof. exact: (fill_prim_steps [AppLCtx _]). Qed.

Lemma prim_steps_tapp_congruence2 {t1 t2 v}:
  prim_steps t1 t2 →
  prim_steps (tapp (tv v) t1) (tapp (tv v) t2).
Proof. exact: (fill_prim_steps [AppRCtx v]). Qed.

Lemma prim_steps_tapp_congruence {t1 t2 v1 v2}:
  prim_steps t1 (tv v1) →
  prim_steps t2 (tv v2) →
  prim_steps (tapp t1 t2) (tapp (tv v1) (tv v2)).
Proof.
  intros Hs1 Hs2.
  eapply rtc_transitive, prim_steps_tapp_congruence2, Hs2.
  eapply prim_steps_tapp_congruence1, Hs1.
Qed.

(* Copy-paste *)
Lemma prim_steps_tbin_congruence1 {b t1 t2 u}:
  prim_steps t1 t2 →
  prim_steps (tbin b t1 u) (tbin b t2 u).
Proof. exact: (fill_prim_steps [BinLCtx _ _]). Qed.

Lemma prim_steps_tbin_congruence2 {b t1 t2 v}:
  prim_steps t1 t2 →
  prim_steps (tbin b (tv v) t1) (tbin b (tv v) t2).
Proof. exact: (fill_prim_steps [BinRCtx _ v]). Qed.

Lemma prim_steps_tbin_congruence {b t1 t2 v1 v2}:
  prim_steps t1 (tv v1) →
  prim_steps t2 (tv v2) →
  prim_steps (tbin b t1 t2) (tbin b (tv v1) (tv v2)).
Proof.
  intros Hs1 Hs2.
  eapply rtc_transitive, prim_steps_tbin_congruence2, Hs2.
  eapply prim_steps_tbin_congruence1, Hs1.
Qed.

Lemma prim_steps_tproj_congruence {e1 e2 l}:
  prim_steps e1 e2 → prim_steps (tproj e1 l) (tproj e2 l).
Proof. exact: (fill_prim_steps [ProjCtx _]). Qed.

Lemma prim_steps_tif_congruence {e1 e2 et ee}:
  prim_steps e1 e2 → prim_steps (tif e1 et ee) (tif e2 et ee).
Proof. exact: (fill_prim_steps [IfCtx _ _]). Qed.

Lemma tskip_prim_steps_to_erasure_of e1 e2 :
  prim_steps_to_erasure_of e1 e2 →
  prim_steps_to_erasure_of (tskip e1) e2.
Proof.
  destruct 1 as [e' [Hs He]]; exists (tskip e'); split_and!; last done.
  apply prim_steps_tskip_congruence, Hs.
Qed.

Lemma erase_dms_index_gen_inv {ds pe l} :
  dms_lookup l (erase_dms ds) = Some (dpt pe) →
  ∃ p, dms_lookup l ds = Some (dpt p) ∧ erase_pt p = pe.
Proof.
  elim: ds => [//|[l' d] ds IHds]; cbn => Hl.
  case_decide; simplify_eq/=; eauto.
  destruct d; simplify_eq/=; eauto.
Qed.

Lemma erase_objLookup_inv {v l pe} :
  erase_vl v @ l ↘ dpt pe →
  ∃ p, v @ l ↘ dpt p ∧ erase_pt p = pe.
Proof.
  move => [dse [Heqe]]; destruct v as [| | |ds]; simplify_eq/=;
    rewrite erase_selfSubst => Hl.
  have [p [Heq He]] := erase_dms_index_gen_inv Hl; naive_solver.
Qed.

Lemma erase_bin_op_eval_inv {b v1 v2 ve}:
  bin_op_eval b (erase_vl v1) (erase_vl v2) = Some ve →
  ∃ v, bin_op_eval b v1 v2 = Some v ∧ erase_vl v = ve.
Proof.
  intros Hop.
  destruct b, v1; simplify_eq/=; destruct v2; simplify_eq/=;
    repeat (case_match; simplify_eq/=); try by eauto.
Qed.

Lemma head_erase_sim_inv {e1 e2} :
  head_step (erase_tm e1) () [] e2 () [] →
  prim_steps_to_erasure_of e1 e2.
Proof. (* Probably should use [inversion Hs], but then update the script. *)
  intros Hs; dependent destruction Hs; simplify_eq/=.
  - induction e1; simplify_eq/=; last
      by apply tskip_prim_steps_to_erasure_of; auto.
    move: x H => {IHe1_1 IHe1_2}.
    move => /unerased_value_steps_to_value [w1 [Hs1 Heq1]].
    move => /unerased_value_steps_to_value [w2 [Hs2 Heq2]].
    simplify_eq/=. destruct w1 as [| |e| ]; simplify_eq/=.
    exists e.|[w2/]; rewrite erase_tm_subst_beta; split_and!; last done.
    trans (tapp (tv (vabs e)) (tv w2)); last apply
      rtc_once, head_prim_step, st_beta.
    exact: prim_steps_tapp_congruence.
  - induction e1; simplify_eq/=; last
      by apply tskip_prim_steps_to_erasure_of; auto.
    move: p l0 H x {IHe1} => ep l eHl.
    move => /unerased_value_steps_to_value [w1 [Hs1 Heq1]].
    simplify_eq/=. pose proof eHl as (?&?&eHls).
    destruct w1 as [| | | ds]; simplify_eq/=.
    destruct (erase_objLookup_inv (v := vobj ds) eHl) as (p & Hl & Heq).
    exists (path2tm p); rewrite erase_tm_path2tm Heq; split_and!; last done.
    trans (tproj (tv (vobj ds)) l); last
      apply rtc_once, head_prim_step, st_proj, Hl.
    exact: prim_steps_tproj_congruence.
  - induction e1; simplify_eq/=; last
      by apply tskip_prim_steps_to_erasure_of; auto.
  - induction e1; simplify_eq/=; first
      by apply tskip_prim_steps_to_erasure_of; auto.
    move: v u0 H H0 {IHe1} => ve u Hope.
    move => /unerased_value_steps_to_value [w1 [Hs1 Heq1]].
    have [v [Hop Heq]] : ∃ v, un_op_eval u w1 = Some v ∧ erase_vl v = ve by
      destruct w1, u; simplify_eq/=; destruct b; simplify_eq/=; eauto.
    exists (tv v); rewrite /= Heq; split_and; last done.
    trans (tun u (tv w1)); last
      apply rtc_once, head_prim_step, st_un, Hop.
    eapply rtc_congruence, Hs1; intros; exact: (fill_prim_step [UnCtx _]).
  - induction e1; simplify_eq/=; first
      by apply tskip_prim_steps_to_erasure_of; auto.
    move: v b0 H H0 H1 {IHe1_1 IHe1_2} => ve b Hope.
    move => /unerased_value_steps_to_value [w1 [Hs1 Heq1]].
    move => /unerased_value_steps_to_value [w2 [Hs2 Heq2]].
    simplify_eq/=.
    have [v [Hop Heq]] := erase_bin_op_eval_inv Hope.
    exists (tv v); rewrite /= Heq; split_and; last done.
    trans (tbin b (tv w1) (tv w2)); last
      apply rtc_once, head_prim_step, st_bin, Hop.
    exact: prim_steps_tbin_congruence.
  - induction e1; simplify_eq/=; first
      by apply tskip_prim_steps_to_erasure_of; auto.
    move: {IHe1_1 IHe1_2 IHe1_3} x.
    move => /unerased_value_steps_to_value [w1 [Hs1 Heq1]].
    destruct w1; simplify_eq/=.
    exists e1_2; split_and!; last done.
    trans (tif (tv (vbool true)) e1_2 e1_3); last
      apply rtc_once, head_prim_step, st_iftrue.
    exact: prim_steps_tif_congruence.
  - induction e1; simplify_eq/=; first
      by apply tskip_prim_steps_to_erasure_of; auto.
    move: {IHe1_1 IHe1_2 IHe1_3} x.
    move => /unerased_value_steps_to_value [w1 [Hs1 Heq1]].
    destruct w1; simplify_eq/=.
    exists e1_3; split_and!; last done.
    trans (tif (tv (vbool false)) e1_2 e1_3); last
      apply rtc_once, head_prim_step, st_iffalse.
    exact: prim_steps_tif_congruence.
Qed.

Hint Constructors rtc : core.
Lemma fill_item_erase_split {e Ke eKe} : erase_tm e = fill_item Ke eKe →
  ∃ Ks eK, prim_steps e (fill Ks eK) ∧ [Ke] = erase_ctxi_list Ks ∧ eKe = erase_tm eK.
Proof.
  move: Ke eKe; induction e; intros; simplify_eq/=.
  4: {
    edestruct (IHe Ke) as (Ks & eK & ?) => //; ev.
    exists (Ks ++ [SkipCtx]), eK; cbn.
    rewrite fill_app erase_ectx_app /= app_nil_r; split_and! => //.
    exact: prim_steps_tskip_congruence.
  }

  (* Clear unused induction hypotheses *)
  all: try clear IHe; try clear IHe1; try clear IHe2; try clear IHe3.
  all: destruct Ke eqn:?; try by simplify_eq/=.
  all: try by [exists [Ke], e; naive_solver]; simplify_eq/=.
  - by exists [AppLCtx e2]; naive_solver.
  - destruct e1; simplify_eq/=; first by exists [AppRCtx v], e2; eauto.
    edestruct unerased_value_steps_to_value as (v1'&?&?); first done.
    exists [AppRCtx v1'], e2; cbn; simplify_eq; split_and! => //.
    by eapply prim_steps_tapp_congruence1, tskip_preserves_termination.
  - exists [BinLCtx b0 e2]; naive_solver.
  - destruct e1; simplify_eq/=; first by exists [BinRCtx b0 v]; cbn; eauto.
    edestruct unerased_value_steps_to_value as (v1'&?&?); first done.
    exists [BinRCtx b0 v1'], e2; cbn; simplify_eq; split_and! => //.
    by eapply prim_steps_tbin_congruence1, tskip_preserves_termination.
  - exists [IfCtx e2 e3]; naive_solver.
Qed.

Lemma fill_erase_split {e Kse eKe} : erase_tm e = fill Kse eKe →
  ∃ Ks eK, prim_steps e (fill Ks eK) ∧ Kse = erase_ctxi_list Ks ∧ eKe = erase_tm eK.
Proof.
  move: e eKe; induction Kse as [|Ke Kse] using rev_ind => e eKe.
  by move => /= <-; exists []; naive_solver.
  rewrite fill_app /= => /fill_item_erase_split [Ks [eK [Hs [HKs Hf]]]].
  destruct (IHKse eK eKe) as [IKs [IeK [IHs [IHKs IHf]]]]; first done.
  exists (IKs ++ Ks), IeK.
  rewrite fill_app /erase_ctxi_list bind_app /= HKs IHKs; split_and! => //.
  trans (fill Ks eK); [exact: Hs | exact: fill_prim_steps IHs].
Qed.

Lemma prim_erase_sim_inv e1 ee2 :
  prim_step (erase_tm e1) () [] ee2 () [] →
  prim_steps_to_erasure_of e1 ee2.
Proof.
  intros Hs1.
  inversion Hs1 as [eKs eKe1 eKe2 Heq1 Heq2 Hh]; simplify_eq/=.
  destruct (fill_erase_split Heq1) as (Ks & eK & Hs & HKs & HeKe1).
  move: (Hh); rewrite HeKe1 => /head_erase_sim_inv [eK2 [Hs' Heq]].
  exists (fill Ks eK2); split_and!; last by rewrite erase_ctxi_fill Heq HKs.
  trans (fill Ks eK); [exact: Hs | exact: fill_prim_steps Hs'].
Qed.

Lemma prims_erase_sim_inv e1 ee2 :
  prim_steps (erase_tm e1) ee2 →
  prim_steps_to_erasure_of e1 ee2.
Proof.
  move => Hereds; hnf; dependent induction Hereds; first by eauto.
  edestruct prim_erase_sim_inv as [e2 [Hreds He]]; first done.
  edestruct (IHHereds e2) as [e3 [Hreds' He']]; first done.
  exists e3; split_and! => //.
  by etrans.
Qed.

(* Cleanup this mess. *)
Definition diverges' e := ∀ e', prim_steps e e' → reducible e' ().
(* weaker than terminates in general, tho here evaluation is deterministic. *)
Definition terminates' e := ∃ v, prim_steps e (tv v).
Definition safe' (e : tm) :=
  ∀ e', prim_steps e e' →
    is_Some (to_val e') ∨ reducible e' ().

Lemma diverges_terminates e: safe' e → ~terminates' e → diverges' e.
Proof.
  move=> Hsafe HnotConv e' Hred.
  have Hnot: ∀ v, ~prim_steps e (of_val v) by clear -HnotConv; firstorder.
  have [[v Hv]|Hr]:= Hsafe _ Hred; last done.
  by rewrite -(of_to_val e' v) in Hred; [destruct (Hnot _ Hred)|].
Qed.

(* From Coq Require Import Classical_Prop. *)
From Coq Require Import ClassicalFacts.

Lemma halting_oracle e : excluded_middle → safe' e → terminates' e ∨ diverges' e.
Proof.
  move=> classic Hsafe.
  have Himpl := diverges_terminates e Hsafe.
  have ?: terminates' e ∨ ~terminates' e by exact: classic.
  intuition.
Qed.

Lemma same_skel_reducible_no_obs {e}:
  reducible e () → reducible (erase_tm e) ().
Proof.
  intros (e'&()&efs&Hstep)%reducible_reducible_no_obs;
    prim_step_inversion Hstep; hnf.
  destruct (simulation_skiperase _ _ Hstep) as [|]; last naive_solver.
  (* FALSE! *)
  eapply reducible_no_obs_reducible; hnf; simpl.
Abort.

(* Lemma erase_reducible e :
  reducible e () → reducible (erase_tm e) ().
Proof.
  intros Hr. *)

(* Lemma same_skel_reducible_no_obs {e e_s σ}:
  reducible_no_obs e_s σ → reducible_no_obs e σ.
Proof.
  intros Hskel (e_s'&σ'&efs&Hstep); prim_step_inversion Hstep.
  destruct (simulation_skeleton _ Hskel Hstep) as (e' & ? & ?).
  exists e'; eauto.
Qed.

Lemma same_skel_reducible {e e_s σ}:
  same_skel_tm e_s e → reducible e_s σ → reducible e σ.
Proof.
  move => Hskel /reducible_reducible_no_obs Hred.
  by eapply reducible_no_obs_reducible, same_skel_reducible_no_obs.
Qed. *)

Lemma safe_skiperase {e}:
  safe e → safe (erase_tm e).
Proof.
  rewrite /safe => Hsafe ee' /pure_steps_erased'.
  destruct dummyState => /erased_prim_steps Hereds'.
  destruct (prims_erase_sim_inv e _ Hereds') as [e' [Hreds %erased_prim_steps He]].

  destruct (Hsafe e') as [Hv|Hr];
    [by apply pure_steps_erased'; destruct dummyState | left|]; simplify_eq/=.
  - destruct e'; try by [case (is_Some_None Hv)]; eauto.
  - destruct Hr.
  (* pose proof (Hsafe e'). *)
  (* destruct e; simplify_eq/=.
  pose proof (simulation_skiperase_erased_steps Hred Hin) as Hst. *)
Abort.

Lemma safe_skiperase_inv {e}:
  safe (erase_tm e) → safe e.
Proof.
  (* rewrite /safe => Hsafe e' > Hred Hin.
  pose proof (simulation_skiperase_erased_steps Hred Hin) as Hst.
  edestruct Hsafe as [Hs|Hs]; [apply Hst|apply elem_of_list_here| |right].
  - destruct e'; try by [case (is_Some_None Hs)]; first naive_solver.
    right; exists [], e', (), [].
    hnf.
    eapply Ectx_step with (K := []) => //.
    (* econstructor.
    eauto.
    apply _.

    naive_solver.
  - eapply same_skel_reducible, Hs; exact: same_skel_symm_tm. *) *)
Abort.

From D.Dot Require Import skeleton_termination.

Lemma prim_steps_det {e1 e2 v}:
  prim_steps e1 (tv v) →
  prim_steps e1 e2 →
  prim_steps e2 (tv v).
Proof.
  move=> Hv Hr; elim: Hr Hv => [//|x y z H Hr IHHr] Hv.
  inversion Hv as [|? y0]; subst; first by edestruct (val_irreducible (tv v)); eauto.
  have ?: y = y0 by [exact: prim_step_det]; subst y0.
  exact: IHHr.
Qed.

(* Theorem rtc_erased_step_inversion'' {t1 σ σ' thp} :
  rtc erased_step ([t1], σ) (thp, σ') →
  ∃ t2, thp = [t2].
Proof.
  move=> Hs; have [t2' ?] := rtc_erased_step_inversion' Hs; subst; eauto.
Qed. *)

Lemma rtc_erased_steps_det {e v thp}:
  rtc erased_step ([e], ()) ([tv v], ()) →
  rtc erased_step ([e], ()) (thp, ()) →
  rtc erased_step (thp, ()) ([tv v], ()).
Proof.
  rewrite erased_prim_steps => H1 H2.
  destruct (rtc_erased_step_inversion' H2) as [e']; simplify_eq.
  move: H2; rewrite !erased_prim_steps => H2.
  exact: prim_steps_det.
Qed.


Lemma safe_erase_to_val {e1 v2}:
  prim_steps e1 (tv v2) →
  safe (erase_tm e1).
Proof.
  rewrite /safe => /erased_prim_steps /simulation_skiperase_erased_steps_vl
    /= Hsafe e' /pure_steps_erased' Hred.
  destruct dummyState.
  (* destruct (rtc_erased_step_inversion' Hred) as [e'' ?]; simplify_eq.
  move: Hin; rewrite elem_of_list_singleton => ?; subst e''. *)
  pose proof (rtc_erased_steps_det Hsafe Hred) as Hremaining.
  destruct (rtc_inv _ _ Hremaining) as [|Hrem]; simplify_eq/=.
  - left; eauto.
  - right; destruct Hrem as [[thp []] [Hrred%erased_step_inversion _]].
    hnf; naive_solver.
Qed.

Lemma safe_erase_diverging {e1}:
  diverges' e1 →
  safe (erase_tm e1).
Proof.
  rewrite /safe /diverges' => /= Hdiv ee2 /pure_steps_erased'.
  case: dummyState => /erased_prim_steps Hereds'.
  (* destruct (rtc_erased_step_inversion'' Hred) as [e'' ?]; simplify_eq.
  have /erased_prim_steps Hereds := (rtc_erased_step_inversion Hred Hin). *)
  (* move => {Hin Hred}. *)
  (* %erased_prim_steps *)
  destruct (prims_erase_sim_inv _ _ Hereds') as [e2 [Hreds He]]; subst.
  have Hrede2 := Hdiv _ Hreds.
  (* What now? *)
Admitted.

Lemma safe'_erase_diverging {e1}:
  diverges' e1 →
  safe' (erase_tm e1).
Proof.
  rewrite /safe' /diverges' => /= Hdiv ee2 Hereds.
  destruct (prims_erase_sim_inv _ _ Hereds) as [e2 [Hreds He]]; subst.
  have Hrede2 := Hdiv _ Hreds.
  (* What now? *)
Admitted.

Definition divergeR {A} (R : relation A) x := ∀ y, rtc R x y → ∃ z, R y z.
Lemma not_divergeR_lt x: ~(divergeR gt x).
Proof.
  rewrite /divergeR => Hdiv.
  induction x; first by destruct (Hdiv 0); [|lia].
  apply: IHx; intros * Hgts. apply: Hdiv.
  eapply rtc_transitive, Hgts; apply rtc_once. lia.
Qed.

Lemma reducible_erase_diverging {e1}:
  diverges' e1 →
  reducible (erase_tm e1) ().
Proof.
Abort.

Lemma safe_erase {e} : excluded_middle → safe' e → safe (erase_tm e).
Proof.
  move=> classic Hsafe.
  have [[??]|?]:= halting_oracle e classic Hsafe.
  exact: safe_erase_to_val.
  exact: safe_erase_diverging.
Qed.

(* Lemma fill_erase_expr {e e1 Ks} :
  erase_tm e = fill Ks e1 →
  ∃ Ks' e1', Ks
  Ks =
e1 = erase_tm e1. *)
(*
Lemma idem_erase_mut :
  (∀ e, erase_tm (erase_tm e) = erase_tm e) ∧
  (∀ v, erase_vl (erase_vl v) = erase_vl v) ∧
  (∀ d, erase_dm (erase_dm d) = erase_dm d) ∧
  (∀ p, erase_pt (erase_pt p) = erase_pt p) ∧
  (∀ T, erase_ty (erase_ty T) = erase_ty T).
Proof.
  apply syntax_mut_ind; simplify_eq/=; try (naive_solver eauto with f_equal);
    intros; f_equal; [generalize dependent ds | generalize dependent vs];
    elim => [//|x xs IHxs] Hxs'; ev; cbn; inversion Hxs' as [|?? Hx Hxs];
    eauto with f_equal.
Qed.

Lemma idem_erase_tm :
  ∀ e, erase_tm (erase_tm e) = erase_tm e.
Proof. apply idem_erase_mut. Qed.

Lemma idemp_fill_item_erase_split {e eK K} : erase_tm e = fill_item K eK →
  eK = erase_tm eK ∧ [K] = erase_ctxi K.
Proof.
  move: e eK; induction K => e eK Heq /=; simplify_eq/=.
  all: try by move: eK Heq; induction e => eK Heq; simplify_eq/=; rewrite ?idem_erase_tm; eauto.
  all: move: (Heq) => /(f_equal erase_tm); rewrite idem_erase_tm /= Heq => -[??]; split_and; eauto with f_equal.
Qed.

Lemma idemp_fill_erase_split {e e1 Ks} : erase_tm e = fill Ks e1 →
  e1 = erase_tm e1 ∧ Ks = erase_ctxi_list Ks.
Proof.
  move: e e1; induction Ks as [|K Ks] using rev_ind => e e1.
  by move => /= <-; rewrite idem_erase_tm.
  rewrite fill_app /= => /idemp_fill_item_erase_split [Heq Heq2].
  edestruct IHKs as [H1 H2]. done.
  split_and => //.
  by rewrite /erase_ctxi_list bind_app /= app_nil_r Heq2 {1}H2.
Qed.

Lemma idemp_fill_erase_expr {e e1 Ks} : erase_tm e = fill Ks e1 →
  e1 = erase_tm e1.
Proof. intros; unmut_lemma (@idemp_fill_erase_split e e1 Ks). Qed.
Lemma idemp_fill_erase_ectx {e e1 Ks}: erase_tm e = fill Ks e1 →
  Ks = erase_ctxi_list Ks.
Proof. intros; unmut_lemma (@idemp_fill_erase_split e e1 Ks). Qed. *)

(* Lemma safe_skiperase {e}:
  safe e → safe (erase_tm e).
Proof.
  rewrite /safe => Hsafe e' thp [] [].
  rewrite erased_prim_steps. => Hred Hin. *)
