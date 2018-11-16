(** Define translation from syntactic terms/values to semantic ones, following Sec. 3.2 of the PDF. *)
From Dot Require Import tactics synFuncs operational.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.
Import operational.lang.

Section Sec.
  Context `{HdotG: dotG Σ}.
  Context `{dotUInterpG Σ}.

  (** We define the translation relation T between syntactic and semantic
      values, terms, types, and so on.
      XXX: we need to distinguish the result of this translation on types from
      the results of the interpretation of types. Right now, we'd use semantic
      types for both.

      Maybe we should talk about source syntax vs translated syntax; we'd hence
      have source types, translated types and semantic types.
   *)

  (** Translation between syntactic and semantic *type member definitions*.
    This is the interesting case of the translation. *)
  Definition t_dty_syn2sem (t_ty: vls -> ty -> ty -> iProp Σ) (T1: ty) (σ σ2: vls) γ2: iProp Σ :=
    (∃ φ T2, γ2 ⤇ φ ∧ t_ty σ T1 T2 ∧
             ∀ ρ v,
               (* We should demand that ρ is closed, and we should check that FV (T) ⊂ dom σ *)
               dot_uinterp T2 (subst_sigma σ ρ, v) ≡ φ (subst_sigma σ2 ρ, v))%I.

  (** Lift translation between syntactic and semantic entities throughout the whole language.
      Lift [t_dty_syn2sem] throughout the syntax of terms and types, checking that otherwise the terms are equal.
   *)
  Fixpoint t_tm (σ: vls) (t1 t2: tm): iProp Σ :=
    match (t1, t2) with
    | (tv v1, tv v2) => t_vl σ v1 v2
    | (tapp t11 t12, tapp t21 t22) =>
      t_tm σ t11 t21 ∧ t_tm σ t12 t22
    | (tproj t1 l1, tproj t2 l2) =>
      t_tm σ t1 t2 ∧ ⌜l1 = l2⌝
    | _ => False
    end%I
  with
  t_vl (σ: vls) (v1 v2: vl): iProp Σ :=
    match (v1, v2) with
    | (var_vl i1, var_vl i2) => ⌜i1 = i2⌝
    | (vabs t1, vabs t2) => t_tm (push_var σ) t1 t2
    | (vobj ds1, vobj ds2) => t_dms (push_var σ) ds1 ds2
    | _ => False
    end%I
  with
  t_dms (σ: vls) (ds1 ds2: dms): iProp Σ :=
    match (ds1, ds2) with
    | (dnil, dnil) => True
    | (dcons d1 ds1, dcons d2 ds2) =>
      t_dm σ d1 d2 ∧ t_dms σ ds1 ds2
    | _ => False
    end%I
  with
  t_dm (σ: vls) (d1 d2: dm): iProp Σ :=
    match (d1, d2) with
    | (dtysyn T1, dtysem σ2 γ2) =>
      (* Only nontrivial case *)
      t_dty_syn2sem t_ty T1 σ σ2 γ2
    | (dvl v1, dvl v2) => t_vl σ v1 v2
    | _ => False
    end%I
  with
  t_path (σ: vls) (p1 p2: path): iProp Σ :=
    match (p1, p2) with
    | (pv v1, pv v2) => t_vl σ v1 v2
    | (pself p1 l1, pself p2 l2) => t_path σ p1 p2 ∧ ⌜l1 = l2⌝
    | _ => False
    end%I
  with
  t_ty (σ: vls) (T1 T2: ty): iProp Σ :=
    match (T1, T2) with
    | (TTop, TTop) => True
    | (TBot, TBot) => True
    | (TAnd T11 T12, TAnd T21 T22) =>
      t_ty σ T11 T21 ∧ t_ty σ T12 T22
    | (TOr T11 T12, TOr T21 T22) =>
      t_ty σ T11 T21 ∧ t_ty σ T12 T22
    | (TLater T1, TLater T2) =>
      t_ty σ T1 T2
    | (TAll T11 T12, TAll T21 T22) =>
      t_ty σ T11 T21 ∧ t_ty (push_var σ) T12 T22
    | (TMu T1, TMu T2) =>
      t_ty (push_var σ) T1 T2
    | (TVMem l1 T1, TVMem l2 T2) => ⌜l1 = l2⌝ ∧ t_ty σ T1 T2
    | (TTMem l1 T11 T12, TTMem l2 T21 T22) => ⌜l1 = l2⌝ ∧ t_ty σ T11 T21 ∧ t_ty σ T12 T22
    | (TSel p1 l1, TSel p2 l2) => t_path σ p1 p2 ∧ ⌜l1 = l2⌝
    | (TSelA p1 l1 T11 T12, TSelA p2 l2 T21 T22) => t_path σ p1 p2 ∧ ⌜l1 = l2⌝ ∧ t_ty σ T11 T21 ∧ t_ty σ T12 T22
    | _ => False
    end%I
  .

  (** Translation for value sequences [vls]. Probably unused. *)
  Fixpoint t_vls (σ: vls) (vs1 vs2: vls): iProp Σ :=
    match (vs1, vs2) with
    | (vlnil, vlnil) => True
    | (vlcons d1 ds1, vlcons d2 ds2) =>
      t_vl σ d1 d2 ∧ t_vls σ ds1 ds2
    | _ => False
    end%I.

  (** For each type T, we can save its interpretation in the ghost state.
      Caveat: you only want to use this on translated (semantic) types. Not to
      be confused with the results of the interpretation (ARGH).
   *)
  Lemma alloc_sp T:
    (|==> ∃ γ, SP γ (dot_uinterp T))%I.
  Proof. by apply saved_pred_alloc. Qed.

  (** The translation relation is persistent. *)
  Lemma t_ty_persistent t1 t2 σ: Persistent (t_ty σ t1 t2)
  with  t_path_persistent t1 t2 σ: Persistent (t_path σ t1 t2)
  with  t_vl_persistent t1 t2 σ: Persistent (t_vl σ t1 t2)
  with  t_tm_persistent t1 t2 σ: Persistent (t_tm σ t1 t2)
  with  t_dm_persistent t1 t2 σ: Persistent (t_dm σ t1 t2)
  with  t_dms_persistent t1 t2 σ: Persistent (t_dms σ t1 t2).
  Proof.
    all: revert t1 t2 σ; induction t1; destruct t2; simpl;
      try apply _.
  Qed.
  Global Existing Instance t_ty_persistent.
  Global Existing Instance t_path_persistent.
  Global Existing Instance t_vl_persistent.
  Global Existing Instance t_tm_persistent.
  Global Existing Instance t_dm_persistent.
  Global Existing Instance t_dms_persistent.

  (** We now prove the lemmas on *existence of translations*, in stages.
      FIXME: unlike on paper, we do not yet check free variables.
   *)

  (** Existence of translations for type member definitions. *)
  Lemma ex_t_dty T1 T2 σ:
    t_ty σ T1 T2 -∗
    (|==> ∃(d: dm), t_dm σ (dtysyn T1) d)%I.
  Proof.
    iMod (alloc_sp T2) as (γ) "#Hγ".
    iIntros "#HT !> /=".
    rewrite /t_dty_syn2sem.
    by iExists (dtysem σ γ), (dot_uinterp T2), T2; repeat iSplit.
  Qed.

  (** is_syn_* are predicates to distinguish syntactic entities/source syntax.
      They also check for free variables at the same time, but that's probably a bad idea.
   *)
  Fixpoint is_syn_tm (n: nat) (t: tm): Prop :=
    match t with
    | tv v =>
      is_syn_vl n v
    | tapp t1 t2 =>
      is_syn_tm n t1 ∧ is_syn_tm n t2
    | tproj t l =>
      is_syn_tm n t
    end
  with
  is_syn_vl (n: nat) (v1: vl): Prop :=
    match v1 with
    | var_vl i => i < n
    | vabs t => is_syn_tm (S n) t
    | vobj ds => is_syn_dms (S n) ds
    end
  with
  is_syn_dms (n: nat) (ds: dms): Prop :=
    match ds with
    | dnil => True
    | dcons d ds =>
      is_syn_dm n d ∧ is_syn_dms n ds
    end
  with
  is_syn_dm (n: nat) (d: dm): Prop :=
    match d with
    (* Only nontrivial case *)
    | dtysyn T =>
      is_syn_ty n T
    | dtysem _ _ => False
    | dvl v1 => is_syn_vl n v1
    end
  with
  is_syn_path (n: nat) (p1: path): Prop :=
    match p1 with
    | pv v => is_syn_vl n v
    | pself p l => is_syn_path n p
    end
  with
  is_syn_ty (n: nat) (T1: ty): Prop :=
    match T1 with
    | TTop => True
    | TBot => True
    | TAnd T1 T2 =>
      is_syn_ty n T1 ∧ is_syn_ty n T2
    | TOr T1 T2 =>
      is_syn_ty n T1 ∧ is_syn_ty n T2
    | TLater T1 =>
      is_syn_ty n T1
    | TAll T1 T2 =>
      is_syn_ty n T1 ∧ is_syn_ty (S n) T2
    | TMu T =>
      is_syn_ty (S n) T
    | TVMem l T => is_syn_ty n T
    | TTMem l T1 T2 => is_syn_ty n T1 ∧ is_syn_ty n T2
    | TSel p l => is_syn_path n p
    | TSelA p l T1 T2 => is_syn_path n p ∧ is_syn_ty n T1 ∧ is_syn_ty n T2
    end.

  Ltac iModSpec' H xt :=
    iMod H as (xt) "#?"; try intuition eassumption.
  Ltac iModSpec H xt := simpl; iModSpec' H xt.

  Ltac pickSigmaInHp :=
    simpl; repeat match goal with
                  | H : context [?p _ ?t1 ] |- context [?p ?σ ?t1 _] =>
                    let x := fresh "TEMP" in
                    evar (x:nat);
                    specialize (H σ x); subst x;
                    let xt := fresh "t" in
                    iModSpec' H xt
                  end.

  Tactic Notation "finish" uconstr(p) := iIntros "!>"; iExists p; simpl; repeat iSplit; auto.
  Tactic Notation "recursiveTransf" uconstr(p) := pickSigmaInHp; finish p.
  Ltac fill :=
    lazymatch goal with
    | |- context [(∃ t2, ?p ?σ (?c ?t11 ?t12) t2)%I] =>
      recursiveTransf (c _ _)
    | |- context [(∃ t2, ?p ?σ (?c ?t11) t2)%I] =>
      recursiveTransf (c _)
    | |- context [(∃ t2, ?p ?σ ?c t2)%I] =>
      recursiveTransf c
    end.
  Ltac skeleton σ n t1 := revert σ n; induction t1; intros * Hsyn; simpl in Hsyn; try solve [contradiction|fill].

  Lemma ex_t_ty σ n t1: is_syn_ty n t1 -> (|==> ∃t2, t_ty σ t1 t2)%I
  with  ex_t_path σ n t1: is_syn_path n t1 -> (|==> ∃t2, t_path σ t1 t2)%I
  with  ex_t_vl σ n t1: is_syn_vl n t1 -> (|==> ∃t2, t_vl σ t1 t2)%I
  with  ex_t_tm σ n t1: is_syn_tm n t1 -> (|==> ∃t2, t_tm σ t1 t2)%I
  with  ex_t_dm σ n t1: is_syn_dm n t1 -> (|==> ∃t2, t_dm σ t1 t2)%I
  with  ex_t_dms σ n t1: is_syn_dms n t1 -> (|==> ∃t2, t_dms σ t1 t2)%I.
  Proof.
    - skeleton σ n t1.
      + iModSpec (ex_t_path σ n p) p2. finish (TSel _ _).
      + iModSpec (ex_t_path σ n p) p2. recursiveTransf (TSelA _ _ _ _).
    - skeleton σ n t1.
      + iModSpec (ex_t_vl σ n v) v2. finish (pv _).
    - skeleton σ n t1.
      + iModSpec (ex_t_tm (push_var σ) (S n) t) t2. finish (vabs _).
      + iModSpec (ex_t_dms (push_var σ) (S n) d) d2. finish (vobj _).
    - skeleton σ n t1.
      + iModSpec (ex_t_vl σ n v) v2. finish (tv _).
    - skeleton σ n t1.
      + iModSpec (ex_t_ty σ n t) t2. by iApply ex_t_dty.
      + iModSpec (ex_t_vl σ n v) v2. finish (dvl _).
    - skeleton σ n t1.
      + iModSpec (ex_t_dm σ n d) d2. recursiveTransf (dcons _ _).
  Qed.


  Fixpoint same_skel_tm (t1 t2: tm): Prop :=
    match (t1, t2) with
    | (tv v1, tv v2) => same_skel_vl v1 v2
    | (tapp t11 t12, tapp t21 t22) =>
      same_skel_tm t11 t21 ∧ same_skel_tm t12 t22
    | (tproj t1 l1, tproj t2 l2) =>
      same_skel_tm t1 t2 ∧ l1 = l2
    | _ => False
    end
  with
  same_skel_vl (v1 v2: vl): Prop :=
    match (v1, v2) with
    | (var_vl i1, var_vl i2) => i1 = i2
    | (vabs t1, vabs t2) => same_skel_tm t1 t2
    | (vobj ds1, vobj ds2) => same_skel_dms ds1 ds2
    | _ => False
    end
  with
  same_skel_dms (ds1 ds2: dms): Prop :=
    match (ds1, ds2) with
    | (dnil, dnil) => True
    | (dcons d1 ds1, dcons d2 ds2) =>
      same_skel_dm d1 d2 ∧ same_skel_dms ds1 ds2
    | _ => False
    end
  with
  same_skel_dm (d1 d2: dm): Prop :=
    match (d1, d2) with
    | (dtysyn T1, dtysem σ2 γ2) =>
      (* Only nontrivial case *)
      True
    | (dvl v1, dvl v2) => same_skel_vl v1 v2
    | _ => False
    end
  with
  same_skel_path (p1 p2: path): Prop :=
    match (p1, p2) with
    | (pv v1, pv v2) => same_skel_vl v1 v2
    | (pself p1 l1, pself p2 l2) => same_skel_path p1 p2 ∧ l1 = l2
    | _ => False
    end
  with
  same_skel_ty (T1 T2: ty): Prop :=
    match (T1, T2) with
    | (TTop, TTop) => True
    | (TBot, TBot) => True
    | (TAnd T11 T12, TAnd T21 T22) =>
      same_skel_ty T11 T21 ∧ same_skel_ty T12 T22
    | (TOr T11 T12, TOr T21 T22) =>
      same_skel_ty T11 T21 ∧ same_skel_ty T12 T22
    | (TLater T1, TLater T2) =>
      same_skel_ty T1 T2
    | (TAll T11 T12, TAll T21 T22) =>
      same_skel_ty T11 T21 ∧ same_skel_ty T12 T22
    | (TMu T1, TMu T2) =>
      same_skel_ty T1 T2
    | (TVMem l1 T1, TVMem l2 T2) => l1 = l2 ∧ same_skel_ty T1 T2
    | (TTMem l1 T11 T12, TTMem l2 T21 T22) => l1 = l2 ∧ same_skel_ty T11 T21 ∧ same_skel_ty T12 T22
    | (TSel p1 l1, TSel p2 l2) => same_skel_path p1 p2 ∧ l1 = l2
    | (TSelA p1 l1 T11 T12, TSelA p2 l2 T21 T22) => same_skel_path p1 p2 ∧ l1 = l2 ∧ same_skel_ty T11 T21 ∧ same_skel_ty T12 T22
    | _ => False
    end.

  Lemma translation_same_skel σ t t':
    ( t_tm σ t t' → ⌜same_skel_tm t t'⌝)%I
  with translation_same_ty σ t t':
    ( t_ty σ t t' → ⌜same_skel_ty t t'⌝)%I
  with translation_same_path σ t t':
    ( t_path σ t t' → ⌜same_skel_path t t'⌝)%I
  with translation_same_dm σ t t':
    ( t_dm σ t t' → ⌜same_skel_dm t t'⌝)%I
  with translation_same_skel_dms σ t t':
    ( t_dms σ t t' → ⌜same_skel_dms t t'⌝)%I
  with translation_same_skel_vl σ t t':
    ( t_vl σ t t' → ⌜same_skel_vl t t'⌝)%I.
  Proof.
    all: iIntros "Hyp";
      destruct t; destruct t'; simpl; eauto;
      (* by iApply translation_same_skel_vl. *)
      repeat progress (try iSplit);
      try (iDestruct "Hyp" as "[Hyp1 Hyp2]");
      try (iDestruct "Hyp1" as "[Hyp11 Hyp12]");
      try (iDestruct "Hyp2" as "[Hyp21 Hyp22]");
      try (iDestruct "Hyp22" as "[Hyp221 Hyp222]");
      match goal with
      | [ HH: context[?P _ _ _] |- context[?P _ _ _] ] => iApply HH; try done
      | _ => try done
      end.
  Qed.

  Fixpoint same_skel_ectx K K' :=
    match K, K' with
    | AppLCtx e2, AppLCtx e2' => same_skel_tm e2 e2'
    | AppRCtx v1, AppRCtx v1' => same_skel_vl v1 v1'
    | ProjCtx l, ProjCtx l' => l = l'
    | _, _ => False
    end.

  Definition same_skel_list_ectx Ks Ks' :=
    List.Forall2 same_skel_ectx Ks Ks'.

  Lemma same_skel_fill Ks e t':
    same_skel_tm (fill Ks e) t' →
    exists Ks' e',  t' = fill Ks' e' ∧ same_skel_tm e e' ∧ same_skel_list_ectx Ks Ks'.
  Proof. Admitted.

  Lemma same_skel_fill_item Ks Ks' e e':
    same_skel_list_ectx Ks Ks' →
    same_skel_tm e e' →
    same_skel_tm (fill Ks e) (fill Ks' e').
  Admitted.


  Lemma same_skel_subst e e' v v':
    same_skel_tm e e' → same_skel_vl v v' →
    same_skel_tm (e.[v/]) (e'.[v'/]).
  Proof.
  Admitted.

  Lemma same_skel_dms_index ds ds' v l:
    same_skel_dms ds ds' →
    index_dms l (selfSubst ds) = Some (dvl v) →
    exists v', index_dms l (selfSubst ds') = Some (dvl v') ∧ same_skel_vl v v'.
  Proof.
  Admitted.

  Ltac destruct_matches :=
    repeat progress match goal with
                    | H: match ?t with | _ => _ end |- _ => destruct t; try done
                    | H: ?A ∧ ?B |- _ => destruct H
                    end.

   Lemma simulation_skeleton_head t1' t1 t2 σ σ' ts:
    same_skel_tm t1 t1' →
    head_step t1 σ [] t2 σ' ts →
    exists t2', head_step t1' σ [] t2' σ' ts ∧ same_skel_tm t2 t2'.
  Proof.
    move=> Hsk Hhs. inversion Hhs; subst; simpl in *.
    - destruct_matches. eexists. split; first by econstructor. by eapply same_skel_subst.
    - destruct_matches. subst. destruct (same_skel_dms_index ds d v l0 H1 H0) as [? [? ?]]. eexists.
      split; [by econstructor | done].
  Qed.

  Theorem simulation_skeleton t1 t1' t2 σ σ' ts:
    same_skel_tm t1 t1' →
    prim_step t1 σ [] t2 σ' ts →
    exists t2', prim_step t1' σ [] t2' σ' ts ∧ same_skel_tm t2 t2'.
  Proof.
    move=> Hsk Hstep. rewrite /prim_step in Hstep. simpl in *.
    inversion Hstep; subst; simpl in *.
    apply same_skel_fill in Hsk as [Ks' [e' [Hfill [Hskel Hsklsit]]]].  simpl in *.
    eapply simulation_skeleton_head in H2 as [e'' [Hhs Hskk]]; last by eauto.
    exists (fill Ks' e''). subst. split; [econstructor; eauto | by apply same_skel_fill_item].
  Qed.
End Sec.
