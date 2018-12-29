(** Define translation from syntactic terms/values to semantic ones, following Sec. 3.2 of the PDF. *)
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.
From Dot Require Import tactics operational synLemmas.

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
  Definition t_dty_syn2sem (t_ty: ty -> ty -> iProp Σ) T1 σ2 γ2: iProp Σ :=
    (∃ φ2 T2, γ2 ⤇ φ2 ∧ t_ty T1 T2 ∧
             ∀ ρ v,
               ⌜ length ρ = length σ2 ⌝ →
               ⌜ cl_ρ ρ ⌝ →
               dot_interp T2 ρ v ≡ φ2 (subst_sigma σ2 ρ) v)%I.

  (** For each type T, we can save its interpretation in the ghost state.
      Caveat: you only want to use this on translated (semantic) types. Not to
      be confused with the results of the interpretation (ARGH).
   *)
  Lemma alloc_sp T:
    (|==> ∃ γ, γ ⤇ dot_interp T)%I.
  Proof. by apply saved_interp_alloc. Qed.

  (** Existence of translations for type member definitions. *)
  Lemma ex_t_dty_gen T1 T2 n t_ty:
    nclosed T1 n →
    t_ty T1 T2 -∗
    (|==> ∃ σ2 γ2, t_dty_syn2sem t_ty T1 σ2 γ2)%I.
  Proof.
    iMod (alloc_sp T2) as (γ) "#Hγ".
    iIntros (Hcl) "HT !> /=".
    rewrite /t_dty_syn2sem.
    iExists (idsσ n), γ, (dot_interp T2), T2; repeat iSplit; trivial.
    rewrite length_idsσ. iIntros. by rewrite (subst_sigma_idsσ ρ n).
  Qed.

  (** Lift translation between syntactic and semantic entities throughout the whole language.
      Lift [t_dty_syn2sem] throughout the syntax of terms and types, checking that otherwise the terms are equal.
   *)

  Fixpoint t_tm (t1 t2: tm) {struct t1}: iProp Σ :=
    match (t1, t2) with
    | (tv v1, tv v2) => t_vl v1 v2
    | (tapp t11 t12, tapp t21 t22) =>
      t_tm t11 t21 ∧ t_tm t12 t22
    | (tproj t1 l1, tproj t2 l2) =>
      t_tm t1 t2 ∧ ⌜l1 = l2⌝
    | (tskip t1, tskip t2) =>
      t_tm t1 t2
    | _ => False
    end%I
  with
  t_vl (v1 v2: vl) {struct v1}: iProp Σ :=
    match (v1, v2) with
    | (var_vl i1, var_vl i2) => ⌜i1 = i2⌝
    | (vabs t1, vabs t2) => t_tm t1 t2
    | (vobj ds1, vobj ds2) =>
      let fix t_dms (ds1 ds2: dms) : iProp Σ :=
          (* ([∗ list] d1 ; d2 ∈ ds1 ; ds2 , t_dm d1 d2)%I *)
          match (ds1, ds2) with
          | (nil, nil) => True
          | (cons d1 ds1, cons d2 ds2) =>
            t_dm d1 d2 ∧ t_dms ds1 ds2
          | _ => False
          end%I
      in
      t_dms ds1 ds2
    | (vnat n1, vnat n2) => ⌜ n1 = n2 ⌝
    | _ => False
    end%I
  with
  t_dm (d1 d2: dm) {struct d1}: iProp Σ :=
    match (d1, d2) with
    | (dtysyn T1, dtysem σ2 γ2) =>
      (* Only nontrivial case *)
      t_dty_syn2sem t_ty T1 σ2 γ2
    | (dvl v1, dvl v2) => t_vl v1 v2
    | _ => False
    end%I
  with
  t_path (p1 p2: path) {struct p1}: iProp Σ :=
    match (p1, p2) with
    | (pv v1, pv v2) => t_vl v1 v2
    | (pself p1 l1, pself p2 l2) => t_path p1 p2 ∧ ⌜l1 = l2⌝
    | _ => False
    end%I
  with
  t_ty (T1 T2: ty) {struct T1}: iProp Σ :=
    match (T1, T2) with
    | (TTop, TTop) => True
    | (TBot, TBot) => True
    | (TAnd T11 T12, TAnd T21 T22) =>
      t_ty T11 T21 ∧ t_ty T12 T22
    | (TOr T11 T12, TOr T21 T22) =>
      t_ty T11 T21 ∧ t_ty T12 T22
    | (TLater T1, TLater T2) =>
      t_ty T1 T2
    | (TAll T11 T12, TAll T21 T22) =>
      t_ty T11 T21 ∧ t_ty T12 T22
    | (TMu T1, TMu T2) =>
      t_ty T1 T2
    | (TVMem l1 T1, TVMem l2 T2) => ⌜l1 = l2⌝ ∧ t_ty T1 T2
    | (TTMem l1 T11 T12, TTMem l2 T21 T22) => ⌜l1 = l2⌝ ∧ t_ty T11 T21 ∧ t_ty T12 T22
    | (TSel p1 l1, TSel p2 l2) => t_path p1 p2 ∧ ⌜l1 = l2⌝
    | (TSelA p1 l1 T11 T12, TSelA p2 l2 T21 T22) => t_path p1 p2 ∧ ⌜l1 = l2⌝ ∧ t_ty T11 T21 ∧ t_ty T12 T22
    | (TNat, TNat) => True
    | _ => False
    end%I.

  (** Translation for definitions. Used? *)
  (* ([∗ list] d1 ; d2 ∈ ds1 ; ds2 , t_dm σ d1 d2)%I. *)
  Definition t_dms : dms → dms → iProp Σ :=
    fix t_dms (ds1 ds2: dms) : iProp Σ :=
      match (ds1, ds2) with
      | (nil, nil) => True
      | (cons d1 ds1, cons d2 ds2) =>
        t_dm d1 d2 ∧ t_dms ds1 ds2
      | _ => False
      end%I.
  Global Arguments t_dms _ /.

  (** Translation for value sequences [vls]. Probably unused. *)
  Definition t_vls: vls → vls → iProp Σ :=
    fix t_vls (vs1 vs2: vls) : iProp Σ :=
      match (vs1, vs2) with
      | (nil, nil) => True
      | (cons d1 vs1, cons d2 vs2) =>
        t_vl d1 d2 ∧ t_vls vs1 vs2
      | _ => False
      end%I.
    (* ([∗ list] v1 ; v2 ∈ vs1 ; vs2 , t_vl σ v1 v2)%I. *)

  (** The translation relation is persistent. *)
  Lemma t_ty_persistent t1 t2: Persistent (t_ty t1 t2)
  with  t_path_persistent t1 t2: Persistent (t_path t1 t2)
  with  t_vl_persistent t1 t2: Persistent (t_vl t1 t2)
  with  t_tm_persistent t1 t2: Persistent (t_tm t1 t2)
  with  t_dm_persistent t1 t2: Persistent (t_dm t1 t2).
  Proof.
    all: revert t1 t2; induction t1; destruct t2;
      try (revert l0; induction l; destruct l0);
      simpl; try apply _.
  Qed.
  Global Existing Instance t_ty_persistent.
  Global Existing Instance t_path_persistent.
  Global Existing Instance t_vl_persistent.
  Global Existing Instance t_tm_persistent.
  Global Existing Instance t_dm_persistent.

  Lemma t_dms_persistent ds1 ds2: Persistent (t_dms ds1 ds2).
  Proof.
    revert ds1 ds2; induction ds1; destruct ds2; simpl;
      try apply _.
  Qed.
  Global Existing Instance t_dms_persistent.

  (** We now prove the lemmas on *existence of translations*, in stages.
      FIXME: unlike on paper, we do not yet check free variables.
   *)

  (** Existence of translations for type member definitions. *)
  Lemma ex_t_dty T1 T2 n:
    nclosed T1 n →
    t_ty T1 T2 -∗
    (|==> ∃(d: dm), t_dm (dtysyn T1) d)%I.
  Proof.
    iIntros "% #Htr /=".
    iMod (ex_t_dty_gen with "Htr") as (σ γ) "#H" => //. by iExists (dtysem σ γ).
  Qed.

  (** is_syn_* are predicates to distinguish syntactic entities/source syntax.
      They also check for free variables at the same time, but that's probably a bad idea.
   *)
  Fixpoint is_syn_tm (t: tm): Prop :=
    match t with
    | tv v =>
      is_syn_vl v
    | tapp t1 t2 =>
      is_syn_tm t1 ∧ is_syn_tm t2
    | tproj t l =>
      is_syn_tm t
    | tskip t =>
      is_syn_tm t
    end
  with
  is_syn_vl (v1: vl): Prop :=
    match v1 with
    | var_vl i => True
    | vabs t => is_syn_tm t
    | vobj ds =>
      let fix is_syn_dms (ds: dms): Prop :=
          match ds with
          | nil => True
          | cons d ds =>
            is_syn_dm d ∧ is_syn_dms ds
          end
        in
          is_syn_dms ds
    | vnat _ => True
    end
  with
  is_syn_dm (d: dm): Prop :=
    match d with
    (* Only nontrivial case *)
    | dtysyn T =>
      is_syn_ty T
    | dtysem _ _ => False
    | dvl v1 => is_syn_vl v1
    end
  with
  is_syn_path (p1: path): Prop :=
    match p1 with
    | pv v => is_syn_vl v
    | pself p l => is_syn_path p
    end
  with
  is_syn_ty (T1: ty): Prop :=
    match T1 with
    | TTop => True
    | TBot => True
    | TAnd T1 T2 =>
      is_syn_ty T1 ∧ is_syn_ty T2
    | TOr T1 T2 =>
      is_syn_ty T1 ∧ is_syn_ty T2
    | TLater T1 =>
      is_syn_ty T1
    | TAll T1 T2 =>
      is_syn_ty T1 ∧ is_syn_ty T2
    | TMu T =>
      is_syn_ty T
    | TVMem l T => is_syn_ty T
    | TTMem l T1 T2 => is_syn_ty T1 ∧ is_syn_ty T2
    | TSel p l => is_syn_path p
    | TSelA p l T1 T2 => is_syn_path p ∧ is_syn_ty T1 ∧ is_syn_ty T2
    | TNat => True
    end.

  Definition is_syn_dms: dms → Prop :=
    fix is_syn_dms (ds: dms): Prop :=
      match ds with
      | nil => True
      | cons d ds =>
        is_syn_dm d ∧ is_syn_dms ds
      end.

  (** BEWARE!
   Not using Admitted here, as it skips well-foundedness checks, which are
   important here. **)
  Axiom false: False.
  Ltac skipAdmit := exfalso; apply false.

  Ltac solve_inv_fv_congruence_h Hfv :=
    move: Hfv; solve_inv_fv_congruence.

  Ltac iModSpec Hfv H xt :=
    iMod H as (xt) "#?"; try solve [simpl; intuition eassumption | solve_inv_fv_congruence_h Hfv].

  Ltac tailPick Hfv H :=
    let xt := fresh "t" in
    (* idtac H; *)
    iModSpec Hfv H xt; clear H.

  Ltac pickSigmaInHp n Hfv :=
    cbn; rewrite /nclosed /= in Hfv;
    repeat match goal with
           | H : context [(∃ _, ?p ?t1 _)%I ], H2 : context [?t1.|[up _]] |- context [?p ?t1 _] =>
             specialize (H (S n)); tailPick Hfv H; try solve_inv_fv_congruence_h Hfv
           | H : context [(∃ _, ?p ?t1 _)%I ], H2 : context [?t1.|[_]] |- context [?p ?t1 _] =>
             specialize (H n); tailPick Hfv H; try solve_inv_fv_congruence_h Hfv
           (* | H : context [(∃ _, ?p _ _)%I ], H2 : context [?t1.|[_]] |- context [_ ?t1 _] => *)
           (*   idtac H; *)
           (*   specialize (H n t1); tailPick Hfv H; try solve_inv_fv_congruence_h Hfv *)
           end.

  Tactic Notation "finish" uconstr(p) := iIntros "!>"; iExists p; simpl; repeat iSplit; auto.
  Tactic Notation "recursiveTransf" uconstr(p) ident(n) ident(Hfv) := pickSigmaInHp n Hfv; finish p.

  Ltac fill n Hfv :=
    lazymatch goal with
    | |- context [(∃ t2, ?p (?c ?t11 ?t12) t2)%I] =>
      recursiveTransf (c _ _) n Hfv
    | |- context [(∃ t2, ?p (?c ?t11) t2)%I] =>
      recursiveTransf (c _) n Hfv
    | |- context [(∃ t2, ?p ?c t2)%I] =>
      recursiveTransf c n Hfv
    end.
  Ltac skeleton n t1 Hfv := revert n; induction t1; intros * Hfv Hsyn; simpl in Hsyn; try solve [contradiction|fill n Hfv].

  Lemma ex_t_ty n t1: nclosed t1 n → is_syn_ty t1 → (|==> ∃t2, t_ty t1 t2)%I
  with  ex_t_path n t1: nclosed t1 n → is_syn_path t1 -> (|==> ∃t2, t_path t1 t2)%I
  with  ex_t_vl n t1: nclosed_vl t1 n → is_syn_vl t1 -> (|==> ∃t2, t_vl t1 t2)%I
  with  ex_t_tm n t1: nclosed t1 n → is_syn_tm t1 -> (|==> ∃t2, t_tm t1 t2)%I
  with  ex_t_dm n t1: nclosed t1 n → is_syn_dm t1 -> (|==> ∃t2, t_dm t1 t2)%I.
  (* with  ex_t_dms σ n t1: is_syn_dms n t1 -> (|==> ∃t2, t_dms σ t1 t2)%I. *)
  Proof.

  all: skeleton n t1 Hfv.
  - iModSpec Hfv (ex_t_path n p) p2. recursiveTransf (TSel _ _) n Hfv.
  - iModSpec Hfv (ex_t_path n p) p2. recursiveTransf (TSelA _ _ _ _) n Hfv.
  - iModSpec Hfv (ex_t_vl n v) v2. recursiveTransf (pv _) n Hfv.
  - iModSpec Hfv (ex_t_tm (S n) t) t2. recursiveTransf (vabs _) n Hfv.
  - iInduction l as [|d ds] "IHl".
    + by iExists (vobj []).
    + ev.
      have: nclosed d (S n). solve_inv_fv_congruence_h Hfv. move => Hcld.
      iMod (ex_t_dm (S n) d Hcld H0) as (d2) "#Hd".

      have: nclosed_vl (vobj ds) n. by eapply fv_vobj_ds_inv. move => Hclds.
      iMod ("IHl" $! Hclds H1) as (v2) "#Hds". iClear "IHl".

      destruct v2 as [ | | | ds2]; try done.
      iExists (vobj (d2 :: ds2)).
      iModIntro; by iSplit.

  - iModSpec Hfv (ex_t_vl n v) v2. recursiveTransf (tv _) n Hfv.
  - iModSpec Hfv (ex_t_ty n t) t2.
    iApply (ex_t_dty _ _ n); try done.
    solve_inv_fv_congruence_h Hfv.
  - iModSpec Hfv (ex_t_vl n v) v2. recursiveTransf (dvl _) n Hfv.
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

  Lemma translation_same_skel t t':
    ( t_tm t t' → ⌜same_skel_tm t t'⌝)%I
  with translation_same_ty t t':
    ( t_ty t t' → ⌜same_skel_ty t t'⌝)%I
  with translation_same_path t t':
    ( t_path t t' → ⌜same_skel_path t t'⌝)%I
  with translation_same_dm t t':
    ( t_dm t t' → ⌜same_skel_dm t t'⌝)%I
  (* with translation_same_skel_dms t t': *)
  (*   ( t_dms t t' → ⌜same_skel_dms t t'⌝)%I *)
  with translation_same_skel_vl t t':
    ( t_vl t t' → ⌜same_skel_vl t t'⌝)%I.
  Proof.
    Ltac localAuto :=
      match goal with
      | [ HH: context[?P _ _] |- context[?P _ _] ] => iApply HH; try done
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
