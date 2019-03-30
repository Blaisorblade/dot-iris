(** Define translation from syntactic terms/values to semantic ones, following Sec. 3.2 of the PDF. *)
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.
From D Require Import tactics.
From D.Dot Require Import operational skeleton synLemmas.

Section Sec.
  Context `{HdotG: dotG Σ}.
  Context `{dotInterpG Σ}.

  (** We define the translation relation T between syntactic and semantic
      values, terms, types, and so on.
      XXX: we need to distinguish the result of this translation on types from
      the results of the interpretation of types. Right now, we'd use semantic
      types for both.

      Maybe we should talk about unstamped syntax vs stamped syntax; we'd hence
      have unstamped types, stamped types and semantic types.
   *)

  (** Translation between syntactic and semantic *type member definitions*.
    This is the interesting case of the translation. *)
  Definition t_dty_syn2sem (t_ty: ty -> ty -> iProp Σ) T1 σ2 γ2: iProp Σ :=
    (∃ φ2 T2, γ2 ⤇ φ2 ∧ t_ty T1 T2 ∧
             ∀ ρ v,
               ⌜ length ρ = length σ2 ⌝ →
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
  Abort.

  (**
     Eventually we want [ t_ty T T1 -∗ t_ty T T2 -∗ ∀ ρ v, ⟦ T1 ⟧ ρ v ≡ ⟦ T2 ⟧ ρ v ].
     This lemma is meant to be the interesting case of that proof.
   *)
  Lemma t_dty_equiv T σ1 γ1 σ2 γ2 t_ty:
    t_dty_syn2sem t_ty T σ1 γ1 -∗
    t_dty_syn2sem t_ty T σ2 γ2 -∗
    (* XXX Should be implied from the rest! This isn't OK! *)
    ⌜ length σ1 = length σ2 ⌝ -∗
    (□∀ T1 T2 ρ v, t_ty T1 T2 -∗ dot_interp T1 ρ v ≡ dot_interp T2 ρ v) -∗
    ∃ φ1 φ2, γ1 ⤇ φ1 ∗ γ2 ⤇ φ2 ∗
                ∀ ρ v,
                  ⌜ length ρ = length σ1 ⌝ →
                  φ1 (subst_sigma σ1 ρ) v ≡ φ2 (subst_sigma σ2 ρ) v.
  Proof.
  Abort.

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
          | (cons (l1, d1) ds1, cons (l2, d2) ds2) =>
            ⌜l1 = l2⌝ ∧ t_dm d1 d2 ∧ t_dms ds1 ds2
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
    | (TNat, TNat) => True
    | _ => False
    end%I.

  (** Translation for definitions. Used? *)
  (* ([∗ list] d1 ; d2 ∈ ds1 ; ds2 , t_dm σ d1 d2)%I. *)
  Definition t_dms : dms → dms → iProp Σ :=
    fix t_dms (ds1 ds2: dms) : iProp Σ :=
      match (ds1, ds2) with
      | (nil, nil) => True
      | (cons (l1, d1) ds1, cons (l2, d2) ds2) =>
        ⌜l1 = l2⌝ ∧ t_dm d1 d2 ∧ t_dms ds1 ds2
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
    all:
      revert t1 t2; induction t1; destruct t2;
      try (elim: l l0 => [|[l1 d1] ds1 IHds1] [|[l2 d2] ds2]);
      simpl; try apply _.
  Qed.
  Global Existing Instance t_ty_persistent.
  Global Existing Instance t_path_persistent.
  Global Existing Instance t_vl_persistent.
  Global Existing Instance t_tm_persistent.
  Global Existing Instance t_dm_persistent.

  Lemma t_dms_persistent ds1 ds2: Persistent (t_dms ds1 ds2).
  Proof.
    elim: ds1 ds2 => [|[l1 d1] ds1 IHds1] [|[l2 d2] ds2] /=; try apply _.
  Qed.
  Global Existing Instance t_dms_persistent.

  (** We now prove the lemmas on *existence of translations*, in stages.
      FIXME: unlike on paper, we do not yet check free variables.
   *)

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
          | cons (l, d) ds =>
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
    | TNat => True
    end.

  Definition is_syn_dms: dms → Prop :=
    fix is_syn_dms (ds: dms): Prop :=
      match ds with
      | nil => True
      | cons (l, d) ds =>
        is_syn_dm d ∧ is_syn_dms ds
      end.

  Lemma ex_t_ty n t1: nclosed t1 n → is_syn_ty t1 → (|==> ∃t2, t_ty t1 t2)%I
  with  ex_t_path n t1: nclosed t1 n → is_syn_path t1 -> (|==> ∃t2, t_path t1 t2)%I
  with  ex_t_vl n t1: nclosed_vl t1 n → is_syn_vl t1 -> (|==> ∃t2, t_vl t1 t2)%I
  with  ex_t_tm n t1: nclosed t1 n → is_syn_tm t1 -> (|==> ∃t2, t_tm t1 t2)%I
  with  ex_t_dm n t1: nclosed t1 n → is_syn_dm t1 -> (|==> ∃t2, t_dm t1 t2)%I.
  (* with  ex_t_dms σ n t1: is_syn_dms n t1 -> (|==> ∃t2, t_dms σ t1 t2)%I. *)
  Proof.

    (* XXX Temporarily commented out only because it's very slow and details of
       the statement are premature. *)
  (* all: skeleton n t1 Hfv. *)
  (* - iModSpec Hfv (ex_t_path n p) p2. recursiveTransf (TSel _ _) n Hfv. *)
  (* - iModSpec Hfv (ex_t_vl n v) v2. recursiveTransf (pv _) n Hfv. *)
  (* - iModSpec Hfv (ex_t_tm (S n) t) t2. recursiveTransf (vabs _) n Hfv. *)
  (* - iInduction l as [|d ds] "IHl". *)
  (*   + by iExists (vobj []). *)
  (*   + ev. *)
  (*     have: nclosed d (S n). solve_inv_fv_congruence_h Hfv. move => Hcld. *)
  (*     iMod (ex_t_dm (S n) d Hcld H0) as (d2) "#Hd". *)

  (*     have: nclosed_vl (vobj ds) n. by eapply fv_vobj_ds_inv. move => Hclds. *)
  (*     iMod ("IHl" $! Hclds H1) as (v2) "#Hds". iClear "IHl". *)

  (*     destruct v2 as [ | | | ds2]; try done. *)
  (*     iExists (vobj (d2 :: ds2)). *)
  (*     iModIntro; by iSplit. *)

  (* - iModSpec Hfv (ex_t_vl n v) v2. recursiveTransf (tv _) n Hfv. *)
  (* - iModSpec Hfv (ex_t_ty n t) t2. *)
  (*   iApply (ex_t_dty _ _ n); try done. *)
  (*   solve_inv_fv_congruence_h Hfv. *)
  (* - iModSpec Hfv (ex_t_vl n v) v2. recursiveTransf (dvl _) n Hfv. *)
  (* Qed. *)
  Abort.

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
  Abort.

  (** We want to prove that different translations give equivalent lookup
      results. This is the core case of that proof. A better statement might say
      that type lookup on different translation gives "equivalent" results, and
      introduce abbreviations/names for the relevant equivalence and lookup. *)
  (** TODO Reuse more of [t_dty_equiv]. *)
  Lemma t_dm_agree_v0 d d1 d2 σ1 γ1 :
    d1 = dtysem σ1 γ1 →
    t_dm d d1 -∗ t_dm d d2 -∗
    ∃ φ1 φ2 σ2 γ2,
      ⌜ d2 = dtysem σ2 γ2 ⌝ ∧
      γ1 ⤇ φ1 ∧
      γ2 ⤇ φ2 ∧
      ∀ ρ v,
        ⌜ length ρ = length σ1 ⌝ →
        (φ1 (subst_sigma σ1 ρ) v ≡ φ2 (subst_sigma σ2 ρ) v).
  Proof.
  Abort.

  Lemma t_dm_agree d d1 d2 σ1 γ1 φ1:
    d1 = dtysem σ1 γ1 →
    t_dm d d1 -∗ t_dm d d2 -∗
    γ1 ⤇ φ1 -∗
    ∃ σ2 γ2 (φ2: envD Σ), ⌜ d2 = dtysem σ2 γ2 ⌝ ∧ γ2 ⤇ (λ vs, φ2 vs) ∧
                ∀ ρ v,
                  ⌜ length ρ = length σ1 ⌝ →
                  ▷ (φ1 (subst_sigma σ1 ρ) v ≡ φ2 (subst_sigma σ2 ρ) v).
  (* Lemma t_dm_agree d d1 d2 σ1 γ1 φ1: *)
  (*   d1 = dtysem σ1 γ1 → *)
  (*   t_dm d d1 -∗ t_dm d d2 -∗ *)
  (*   γ1 ⤇ φ1 -∗ *)
  (*   ∃ σ2 γ2 φ2, ⌜ d2 = dtysem σ2 γ2 ⌝ ∧ γ2 ⤇ φ2 ∧ *)
  (*               ∀ ρ v, *)
  (*                 ⌜ length ρ = length σ1 ⌝ → *)
  (*                 ⌜ cl_ρ ρ ⌝ → *)
  (*                 ▷ (φ1 (subst_sigma σ1 ρ) v ≡ φ2 (subst_sigma σ2 ρ) v). *)
  Proof.
  Abort.

End Sec.
