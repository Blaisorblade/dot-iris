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
  | vvar _ => v
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

Theorem simulation_skiperase e1 e2 :
  prim_step e1 () [] e2 () [] →
  rtc (λ e1 e2, prim_step e1 () [] e2 () []) (erase_tm e1) (erase_tm e2).
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
  rtc (λ e1 e2, prim_step e1 () [] e2 () []) (erase_tm e1) (erase_tm e2).
Proof.
  intros Hs; prim_step_inversion Hs.
  destruct σ1; exact: simulation_skiperase.
Qed.

Theorem simulation_skiperase_erased_step {t1 t2 σ σ'} :
  erased_step ([t1], σ) ([t2], σ') →
  rtc erased_step ([erase_tm t1], σ) ([erase_tm t2], σ').
Proof.
  rewrite erased_step_prim => /simulation_skiperase' Hstep; destruct σ, σ'.
  eapply (rtc_congruence (λ t, ([t], ()))), Hstep => /= e1 e2 Hs.
  apply erased_step_prim, Hs.
Qed.

Theorem simulation_skiperase_erased_steps {t1 t2 σ σ'} :
  rtc erased_step ([t1], σ) ([t2], σ') →
  rtc erased_step ([erase_tm t1], σ) ([erase_tm t2], σ').
Proof.
  move => Hsteps.
  dependent induction Hsteps; first done.
  destruct y as [l σ'']; have ?: σ'' = σ by destruct σ, σ''; subst.
  move: H (H) => [k Hstep] Hestep.
  have [ti ?] := step_inversion Hstep; destruct_and!; simplify_eq.
  etrans; first exact: (simulation_skiperase_erased_step Hestep).
  exact: IHHsteps.
Qed.

Corollary simulation_skiperase_erased_steps_vl {t1 v2 σ σ'} :
  rtc erased_step ([t1], σ) ([tv v2], σ') →
  rtc erased_step ([erase_tm t1], σ) ([tv (erase_vl v2)], σ').
Proof. exact: (simulation_skiperase_erased_steps (t2 := tv v2)). Qed.
