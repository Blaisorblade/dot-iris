(** Define translation from syntactic terms/values to semantic ones, following Sec. 3.2 of the PDF. *)
From Dot Require Import tactics synFuncs operational.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.
Import operational.lang.

Section Sec.
  Context `{HdotG: dotG Σ}.
  Context `{dotInterpG Σ}.

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
               dot_interp T2 (subst_sigma σ ρ) v ≡ φ (subst_sigma σ2 ρ) v)%I.

  (** Lift translation between syntactic and semantic entities throughout the whole language.
      Lift [t_dty_syn2sem] throughout the syntax of terms and types, checking that otherwise the terms are equal.
   *)

  Fixpoint t_tm (σ: vls) (t1 t2: tm) {struct t1}: iProp Σ :=
    match (t1, t2) with
    | (tv v1, tv v2) => t_vl σ v1 v2
    | (tapp t11 t12, tapp t21 t22) =>
      t_tm σ t11 t21 ∧ t_tm σ t12 t22
    | (tproj t1 l1, tproj t2 l2) =>
      t_tm σ t1 t2 ∧ ⌜l1 = l2⌝
    | (tskip t1, tskip t2) =>
      t_tm σ t1 t2
    | _ => False
    end%I
  with
  t_vl (σ: vls) (v1 v2: vl) {struct v1}: iProp Σ :=
    match (v1, v2) with
    | (var_vl i1, var_vl i2) => ⌜i1 = i2⌝
    | (vabs t1, vabs t2) => t_tm (push_var σ) t1 t2
    | (vobj ds1, vobj ds2) =>
      let fix t_dms (σ: vls) (ds1 ds2: dms) : iProp Σ :=
          (* ([∗ list] d1 ; d2 ∈ ds1 ; ds2 , t_dm σ d1 d2)%I *)
          match (ds1, ds2) with
          | (nil, nil) => True
          | (cons d1 ds1, cons d2 ds2) =>
            t_dm σ d1 d2 ∧ t_dms σ ds1 ds2
          | _ => False
          end%I
      in
      t_dms (push_var σ) ds1 ds2
    | (vnat n1, vnat n2) => ⌜ n1 = n2 ⌝
    | _ => False
    end%I
  with
  t_dm (σ: vls) (d1 d2: dm) {struct d1}: iProp Σ :=
    match (d1, d2) with
    | (dtysyn T1, dtysem σ2 γ2) =>
      (* Only nontrivial case *)
      t_dty_syn2sem t_ty T1 σ σ2 γ2
    | (dvl v1, dvl v2) => t_vl σ v1 v2
    | _ => False
    end%I
  with
  t_path (σ: vls) (p1 p2: path) {struct p1}: iProp Σ :=
    match (p1, p2) with
    | (pv v1, pv v2) => t_vl σ v1 v2
    | (pself p1 l1, pself p2 l2) => t_path σ p1 p2 ∧ ⌜l1 = l2⌝
    | _ => False
    end%I
  with
  t_ty (σ: vls) (T1 T2: ty) {struct T1}: iProp Σ :=
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
    | (TNat, TNat) => True
    | _ => False
    end%I
  .

  (** Translation for definitions. Used? *)
  Definition t_dms (σ: vls) (ds1 ds2: dms) : iProp Σ :=
    ([∗ list] d1 ; d2 ∈ ds1 ; ds2 , t_dm σ d1 d2)%I.
  Global Arguments t_dms _ /.
  (** Translation for value sequences [vls]. Probably unused. *)
  Definition t_vls (σ: vls) (vs1 vs2: vls) : iProp Σ :=
    ([∗ list] v1 ; v2 ∈ vs1 ; vs2 , t_vl σ v1 v2)%I.

  (** For each type T, we can save its interpretation in the ghost state.
      Caveat: you only want to use this on translated (semantic) types. Not to
      be confused with the results of the interpretation (ARGH).
   *)
  Lemma alloc_sp T:
    (|==> ∃ γ, γ ⤇ dot_interp T)%I.
  Proof. by apply saved_interp_alloc. Qed.

  (** The translation relation is persistent. *)
  Lemma t_ty_persistent t1 t2 σ: Persistent (t_ty σ t1 t2)
  with  t_path_persistent t1 t2 σ: Persistent (t_path σ t1 t2)
  with  t_vl_persistent t1 t2 σ: Persistent (t_vl σ t1 t2)
  with  t_tm_persistent t1 t2 σ: Persistent (t_tm σ t1 t2)
  with  t_dm_persistent t1 t2 σ: Persistent (t_dm σ t1 t2).
  Proof.
    all: revert t1 t2 σ; induction t1; destruct t2;
      try (revert l0; induction l; destruct l0);
      simpl; try apply _.
  Qed.
  Global Existing Instance t_ty_persistent.
  Global Existing Instance t_path_persistent.
  Global Existing Instance t_vl_persistent.
  Global Existing Instance t_tm_persistent.
  Global Existing Instance t_dm_persistent.

  Lemma t_dms_persistent ds1 ds2 σ: Persistent (t_dms σ ds1 ds2).
  Proof.
    revert ds1 ds2 σ; induction ds1; destruct ds2; simpl;
      try apply _.
  Qed.
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
    by iExists (dtysem σ γ), (dot_interp T2), T2; repeat iSplit.
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
    | tskip t =>
      is_syn_tm n t
    end
  with
  is_syn_vl (n: nat) (v1: vl): Prop :=
    match v1 with
    | var_vl i => i < n
    | vabs t => is_syn_tm (S n) t
    | vobj ds =>
      let fix is_syn_dms (n: nat) (ds: dms): Prop :=
          match ds with
          | nil => True
          | cons d ds =>
            is_syn_dm n d ∧ is_syn_dms n ds
          end
        in
          is_syn_dms (S n) ds
    | vnat n => True
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
    | TNat => True
    end.

  Definition is_syn_dms (n: nat) (ds: dms): Prop :=
    Forall (is_syn_dm n) ds.

  Ltac iModSpec H xt :=
    iMod H as (xt) "#?"; try intuition eassumption.

  Ltac pickSigmaInHp :=
    cbn; repeat match goal with
                  | H : context [?p _ ?t1 ] |- context [?p ?σ ?t1 _] =>
                    let x := fresh "TEMP" in
                    evar (x:nat);
                    specialize (H σ x); subst x;
                    let xt := fresh "t" in
                    iModSpec H xt
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

  (** BEWARE!
   Not using Admitted here, as it skips well-foundedness checks, which are
   important here. **)
  Axiom false: False.
  Ltac skipAdmit := exfalso; apply false.

  Lemma ex_t_ty σ n t1: is_syn_ty n t1 -> (|==> ∃t2, t_ty σ t1 t2)%I
  with  ex_t_path σ n t1: is_syn_path n t1 -> (|==> ∃t2, t_path σ t1 t2)%I
  with  ex_t_vl σ n t1: is_syn_vl n t1 -> (|==> ∃t2, t_vl σ t1 t2)%I
  with  ex_t_tm σ n t1: is_syn_tm n t1 -> (|==> ∃t2, t_tm σ t1 t2)%I
  with  ex_t_dm σ n t1: is_syn_dm n t1 -> (|==> ∃t2, t_dm σ t1 t2)%I.
  (* with  ex_t_dms σ n t1: is_syn_dms n t1 -> (|==> ∃t2, t_dms σ t1 t2)%I. *)
  Proof.
    - skeleton σ n t1.
      + iModSpec (ex_t_path σ n p) p2. finish (TSel _ _).
      + iModSpec (ex_t_path σ n p) p2. recursiveTransf (TSelA _ _ _ _).
    - skeleton σ n t1.
      + iModSpec (ex_t_vl σ n v) v2. finish (pv _).
    - skeleton σ n t1.
      + iModSpec (ex_t_tm (push_var σ) (S n) t) t2. finish (vabs _).
      +
        (* iModSpec (ex_t_dms (push_var σ) (S n) d) d2. finish (vobj _). *)
        iInduction l as [|d ds] "IHl".
        * by iExists (vobj []).
        * ev.
          iMod (ex_t_dm (push_var σ) (S n) d H0) as (d2) "#Hd".
          iMod ("IHl" $! H1) as (v2) "#Hds". iClear "IHl".
          destruct v2 as [ | | | ds2]; try done.
          iExists (vobj (d2 :: ds2)).
          iModIntro; by iSplit.
    - skeleton σ n t1.
      + iModSpec (ex_t_vl σ n v) v2. finish (tv _).
    - skeleton σ n t1.
      + iModSpec (ex_t_ty σ n t) t2. by iApply ex_t_dty.
      + iModSpec (ex_t_vl σ n v) v2. finish (dvl _).
    (* - skeleton σ n t1. *)
    (*   + iModSpec (ex_t_dm σ n a) d2. recursiveTransf (cons _ _). *)
  Qed.

  Fixpoint same_skel_tm (t1 t2: tm): Prop :=
    match (t1, t2) with
    | (tv v1, tv v2) => same_skel_vl v1 v2
    | (tapp t11 t12, tapp t21 t22) =>
      same_skel_tm t11 t21 ∧ same_skel_tm t12 t22
    | (tproj t1 l1, tproj t2 l2) =>
      same_skel_tm t1 t2 ∧ l1 = l2
    | (tskip t1, tskip t2) =>
      same_skel_tm t1 t2
    | _ => False
    end
  with
  same_skel_vl (v1 v2: vl): Prop :=
    match (v1, v2) with
    | (var_vl i1, var_vl i2) => i1 = i2
    | (vabs t1, vabs t2) => same_skel_tm t1 t2
    | (vobj ds1, vobj ds2) =>
      let fix same_skel_dms (ds1 ds2: dms): Prop :=
          match (ds1, ds2) with
          | (nil, nil) => True
          | (cons d1 ds1, cons d2 ds2) =>
            same_skel_dm d1 d2 ∧ same_skel_dms ds1 ds2
          | _ => False
          end
      in same_skel_dms ds1 ds2
    | (vnat n1, vnat n2) => n1 = n2
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
    end.
  Fixpoint same_skel_path (p1 p2: path): Prop :=
    match (p1, p2) with
    | (pv v1, pv v2) => same_skel_vl v1 v2
    | (pself p1 l1, pself p2 l2) => same_skel_path p1 p2 ∧ l1 = l2
    | _ => False
    end.
  Fixpoint same_skel_ty (T1 T2: ty): Prop :=
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
    | (TNat, TNat) => True
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
  (* with translation_same_skel_dms σ t t': *)
  (*   ( t_dms σ t t' → ⌜same_skel_dms t t'⌝)%I *)
  with translation_same_skel_vl σ t t':
    ( t_vl σ t t' → ⌜same_skel_vl t t'⌝)%I.
  Proof.
    Ltac localAuto :=
      match goal with
      | [ HH: context[?P _ _ _] |- context[?P _ _ _] ] => iApply HH; try done
      | _ => try done
      end.
    all: iIntros "Hyp";
      destruct t; destruct t'; simpl; eauto;
      (* by iApply translation_same_skel_vl. *)
      repeat iSplit;
      try (iDestruct "Hyp" as "[Hyp1 Hyp2]");
      try (iDestruct "Hyp1" as "[Hyp11 Hyp12]");
      try (iDestruct "Hyp2" as "[Hyp21 Hyp22]");
      try (iDestruct "Hyp22" as "[Hyp221 Hyp222]"); localAuto.
    iInduction l as [| d l] "IHl" forall (l0); destruct l0 as [|d0 l0]; try done.
    repeat iSplit;
      try (iDestruct "Hyp" as "[Hyp1 Hyp2]"); localAuto.
    by iApply "IHl".
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

  (* Generalize over all the syntax, and same_skeleton environments. I proved
     same_skel_tm_subst just as a minimal sanity check. *)
  Lemma same_skel_vl_subst e e' v v':
    same_skel_vl e e' → same_skel_vl v v' →
    same_skel_vl (e.[v/]) (e'.[v'/]).
  Proof.
    move: e'; induction e; destruct e';
    move => Hske Hskv;
      cbn in Hske |- *; try inversion Hske; ev; asimpl; auto.
  Admitted.

  (* Just a test proof. *)
  Lemma same_skel_tm_subst e e' v v':
    same_skel_tm e e' → same_skel_vl v v' →
    same_skel_tm (e.|[v/]) (e'.|[v'/]).
  Proof.
    move: e'; induction e; destruct e';
    move => Hske Hskv;
      cbn in Hske |- *; try inversion Hske; ev; asimpl; auto using same_skel_vl_subst.
   Qed.

  Definition same_skel_dms (ds1 ds2: dms): Prop := Forall2 same_skel_dm ds1 ds2.

  Lemma same_skel_dms_index ds ds' v l:
    same_skel_dms ds ds' →
    reverse (selfSubst ds) !! l = Some (dvl v) →
    exists v', reverse (selfSubst ds') !! l = Some (dvl v') ∧ same_skel_vl v v'.
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
    - destruct_matches. eexists. split; first by econstructor. by eapply same_skel_tm_subst.
    - destruct_matches. subst. destruct (same_skel_dms_index ds l1 v l0) as [? [? ?]]; try done.
      + clear Hhs H0. red; generalize dependent l1; induction ds; destruct l1; try constructor; ev; try apply IHds; done.
      + eexists.
      split; [by econstructor | done].
    - destruct_matches. eexists. split; by [econstructor|idtac].
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
