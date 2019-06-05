From iris.proofmode Require Import tactics.
From D Require Export tactics iris_prelude.
From D.Dot Require Export operational.

(** Deduce types from variable names, like on paper, for readability and to help
    type inference for some overloaded operations (e.g. substitution). *)
Implicit Types
         (L T U: ty) (v w: vl) (e: tm) (d: dm) (ds: dms) (p: path)
         (Γ : ctx) (ρ : vls).


(** The logical relation core is the [interp], interprets *open* types into
    predicates over *closed* values. Hence, [interp T ρ v] uses its argument [ρ]
    to interpret anything contained in T, but not things contained in v.

    Semantic judgements must apply instead to open terms/value/paths; therefore,
    they are defined using closing substitution on arguments of [interp].

    Similar comments apply to [def_interp].

    Additionally, both apply to *translated* arguments, hence they only expect
    [dtysem] and not [dtysyn] for type member definitions.
 *)
Section logrel.
  Context `{dlangG Σ}.

  (* Use Program without its extended pattern-matching compiler; we only need
     its handling of coercions. *)
  Unset Program Cases.

  Notation D := (vl -c> iProp Σ).
  Implicit Types (interp : envD Σ) (φ : D).
  Notation envPred s := (vls -c> s -c> iProp Σ).

  Definition def_interp_vmem interp : envPred dm :=
    λ ρ d, (⌜ nclosed d 0 ⌝ ∗ ∃ vmem, ⌜d = dvl vmem⌝ ∧ ▷ interp ρ vmem)%I.
  Global Arguments def_interp_vmem /.

  Definition idm_proj_semtype d φ : iProp Σ :=
    (∃ s σ interp, ⌜ d = dtysem σ s ∧ φ = interp σ ⌝ ∗ s ↝ interp)%I.
  Global Arguments idm_proj_semtype: simpl never.
  Notation "d ↗ φ" := (idm_proj_semtype d φ) (at level 20).

  Lemma stored_pred_agree d φ1 φ2 v :
    d ↗ φ1 -∗ d ↗ φ2 -∗ ▷ (φ1 v ≡ φ2 v).
  Proof.
    iIntros "/= #Hd1 #Hd2".
    iDestruct "Hd2" as (s' σ' interp2 H2) "Hs2".
    iDestruct "Hd1" as (s σ interp1 H1) "Hs1".
    ev; simplify_eq. by iApply (leadsto_agree _ interp1 interp2).
  Qed.

  Definition def_interp_tmem interp1 interp2 : envPred dm :=
    λ ρ d,
    (⌜ nclosed d 0 ⌝ ∗ ∃ φ, (d ↗ φ) ∗
       □ ((∀ v, ⌜ nclosed_vl v 0 ⌝ → ▷ interp1 ρ v → ▷ □ φ v) ∗
          (∀ v, ⌜ nclosed_vl v 0 ⌝ → ▷ □ φ v → ▷ interp2 ρ v)))%I.
  Global Arguments def_interp_tmem /.

  Definition lift_dinterp_vl l (dinterp: envPred dm): envD Σ :=
    λ ρ v, (⌜ nclosed_vl v 0 ⌝ ∗ ∃ d, ⌜v @ l ↘ d⌝ ∧ dinterp ρ d)%I.
  Global Arguments lift_dinterp_vl /.

  Definition interp_vmem l interp : envD Σ :=
    lift_dinterp_vl l (def_interp_vmem interp).
  Global Arguments interp_vmem /.

  Definition interp_tmem l interp1 interp2 : envD Σ :=
    lift_dinterp_vl l (def_interp_tmem interp1 interp2).
  Global Arguments interp_tmem /.

  Definition interp_expr interp : envPred tm :=
    λ ρ t, WP t {{ interp ρ }} %I.
  Global Arguments interp_expr /.

  Definition interp_and interp1 interp2 : envD Σ :=
    λ ρ v, (interp1 ρ v ∧ interp2 ρ v) %I.
  Global Arguments interp_and /.

  Definition interp_or interp1 interp2 : envD Σ :=
    λ ρ v, (interp1 ρ v ∨ interp2 ρ v) %I.
  Global Arguments interp_or /.

  Definition interp_later interp : envD Σ :=
    λ ρ v, (⌜ nclosed_vl v 0 ⌝ ∗ ▷ interp ρ v) % I.
  Global Arguments interp_later /.

  Definition interp_nat : envD Σ := λ ρ v, (∃ n, ⌜v = vnat n⌝) %I.
  Global Arguments interp_nat /.

  Definition interp_top : envD Σ := λ ρ v, ⌜ nclosed_vl v 0 ⌝%I.
  Global Arguments interp_top /.

  Definition interp_bot : envD Σ := λ ρ v, False%I.
  Global Arguments interp_bot /.

  (* Paolo: This definition is contractive (similarly to what's useful for
     equi-recursive types).
     However, I am not sure we need this; it'd be good to
     write an example where this makes a difference.
     I think that would be something like
     nu x. { T = TNat; U = x.T -> x.T }:
     mu (x: {T <: TNat; U <: x.T -> TNat}).
     If the function type constructor is not contractive but only non-expansive,
     typechecking this example needs to establish x.T <: TNat having in context
     only x: {T <: TNat; U <: x.T -> TNat}.
   *)
  Definition interp_forall interp1 interp2 : envD Σ :=
    λ ρ v,
    (⌜ nclosed_vl v 0 ⌝ ∗
       ∃ t, ⌜ v = vabs t ⌝ ∗
       □ ▷ ∀ w, interp1 ρ w → interp_expr interp2 (w :: ρ) t.|[w/])%I.
  Global Arguments interp_forall /.

  Definition interp_mu interp : envD Σ :=
    λ ρ v, interp (v::ρ) v.
  Global Arguments interp_mu /.

  (** A simplified variant of weakest preconditions for path evaluation.
      The difference is that path evaluation is completely pure, and
      postconditions must hold now, not after updating resources.
      vp ("Value from Path") and vq range over results of evaluating paths.

      Path evaluation was initially more complex; now that we got to this
      version, I wonder whether we can just use the standard Iris WP, but I am
      not sure if that would work.
      *)
  Fixpoint path_wp p φ: iProp Σ :=
    match p with
    | pself p l => path_wp p (λ vp, ∃ vq, ⌜ vp @ l ↘ dvl vq ⌝ ∧ ▷ φ vq)
    | pv vp => φ vp
    end%I.

  Global Instance path_wp_persistent φ p:
    (∀ v, Persistent (φ v)) → Persistent (path_wp p φ).
  Proof. elim: p φ => *; apply _. Qed.

  Definition interp_sel p (l: label) : envD Σ :=
    λ ρ v, (⌜ nclosed_vl v 0 ⌝ ∧ path_wp p.|[to_subst ρ]
      (λ vp, ∃ ϕ d, ⌜vp @ l ↘ d⌝ ∧ d ↗ ϕ ∧ ▷ □ ϕ v))%I.
  Global Arguments interp_sel /.

  Fixpoint interp (T: ty) : envD Σ :=
    match T with
    | TTMem l L U => interp_tmem l (interp L) (interp U)
    | TVMem l T' => interp_vmem l (interp T')
    | TAnd T1 T2 => interp_and (interp T1) (interp T2)
    | TOr T1 T2 => interp_or (interp T1) (interp T2)
    | TLater T => interp_later (interp T)
    | TNat => interp_nat
    | TTop => interp_top
    | TBot => interp_bot
    | TAll T1 T2 => interp_forall (interp T1) (interp T2)
    | TMu T => interp_mu (interp T)
    | TSel p l => interp_sel p l
  end % I.

  Global Instance dlang_interp : TyInterp ty Σ := interp.
  Notation "⟦ T ⟧" := (interp T).
  Notation "⟦ T ⟧ₑ" := (interp_expr (interp T)).

  Global Instance interp_persistent T ρ v :
    Persistent (⟦ T ⟧ ρ v).
  Proof. revert v ρ; induction T => v ρ; simpl; try apply _. Qed.

  Fixpoint def_interp (T: ty) : envPred dm :=
    λ ρ d,
    match T with
    | TTMem _ L U => def_interp_tmem (interp L) (interp U) ρ d
    | TVMem _ T' => def_interp_vmem (interp T') ρ d
    | _ => False
    end%I.

  Global Instance def_interp_persistent T ρ d :
    Persistent (def_interp T ρ d).
  Proof. revert ρ d; induction T; simpl; try apply _. Qed.

  Definition defs_interp_and (interp1 interp2 : envPred dms) : envPred dms :=
    λ ρ ds, (interp1 ρ ds ∧ interp2 ρ ds)%I.

  Definition lift_dinterp_dms T : envPred dms := λ ρ ds, (∃ l d,
    ⌜ label_of_ty T = Some l ∧ dms_lookup l ds = Some d ∧ nclosed ds 0 ⌝
    ∧ def_interp T ρ d)%I.

  Fixpoint defs_interp T : envPred dms :=
    match T with
    | TAnd T1 T2 => defs_interp_and (defs_interp T1) (defs_interp T2)
    | TTop => λ ρ ds, ⌜ nclosed ds 0 ⌝
    | _ => lift_dinterp_dms T
    end % I.

  Global Instance defs_interp_persistent T ρ ds : Persistent (defs_interp T ρ ds).
  Proof. revert ds ρ; induction T; cbn; try case_match; try apply _. Qed.

  Fixpoint interp_env (Γ : ctx) (vs : vls) : iProp Σ :=
    match Γ with
    | nil => ⌜vs = nil⌝
    | T :: Γ' =>
      match vs with
      | nil => False
      | v :: ρ => interp_env Γ' ρ ∗ ⟦ T ⟧ (v::ρ) v
      end
    end%I.

  Notation "⟦ Γ ⟧*" := (interp_env Γ).

  Global Instance interp_env_persistent Γ ρ :
    Persistent (⟦ Γ ⟧* ρ).
  Proof. elim: Γ ρ => [|τ Γ IHΓ] [|v ρ]; apply _. Qed.

  Definition defCtxCons Γ V := TLater V :: Γ.

  (** Definitions for semantic (definition) (sub)typing *)
  (** Since [⟦Γ⟧* ρ] might be impossible, we must require closedness explicitly. *)
  Definition idtp Γ T d : iProp Σ :=
    (⌜ nclosed d (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ → def_interp T ρ d.|[to_subst ρ])%I.
  Global Arguments idtp /.
  Notation "Γ ⊨d d : T" := (idtp Γ T d) (at level 64, d, T at next level).

  Lemma idtp_closed Γ T d: Γ ⊨d d : T -∗ ⌜ nclosed d (length Γ) ⌝.
  Proof. iIntros "[$ _]". Qed.

  Definition idstp Γ T ds : iProp Σ :=
    (⌜ nclosed ds (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ → defs_interp T ρ ds.|[to_subst ρ])%I.
  Global Arguments idstp /.
  Notation "Γ ⊨ds ds : T" := (idstp Γ T ds) (at level 74, ds, T at next level).

  Lemma idstp_closed Γ T ds: Γ ⊨ds ds : T -∗ ⌜ nclosed ds (length Γ) ⌝.
  Proof. iIntros "[$ _]". Qed.

  (* Really needed? Try to stop using it. *)
  Definition ivtp Γ T v : iProp Σ := (⌜ nclosed_vl v (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ → ⟦T⟧ ρ v.[to_subst ρ])%I.
  Global Arguments ivtp /.

  Definition ietp Γ T e : iProp Σ := (⌜ nclosed e (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ → ⟦T⟧ₑ ρ (e.|[to_subst ρ]))%I.
  Global Arguments ietp /.
  Notation "Γ ⊨ e : T" := (ietp Γ T e) (at level 74, e, T at next level).

  Lemma ietp_closed Γ T e: Γ ⊨ e : T -∗ ⌜ nclosed e (length Γ) ⌝.
  Proof. iIntros "[$ _]". Qed.

  Definition step_indexed_ietp Γ T e i: iProp Σ :=
    (⌜ nclosed e (length Γ) ⌝ ∗
      □∀ ρ, ⟦Γ⟧* ρ →
      interp_expr (λ ρ v, ▷^i ⟦T⟧ ρ v) ρ (e.|[to_subst ρ]))%I.
  Global Arguments step_indexed_ietp /.
  Notation "Γ ⊨ e : T , i" := (step_indexed_ietp Γ T e i) (at level 74, e, T at next level).

  Lemma step_indexed_ietp_closed Γ T e i: Γ ⊨ e : T, i -∗ ⌜ nclosed e (length Γ) ⌝.
  Proof. iIntros "[$ _]". Qed.

  (** Subtyping. Defined on values. *)
  Definition ivstp Γ T1 T2: iProp Σ := (□∀ ρ v, ⟦Γ⟧* ρ → ⟦T1⟧ ρ v → ⟦T2⟧ ρ v)%I.
  Global Arguments ivstp /.

  (** Indexed Subtyping. Defined on closed values. We must require closedness
      explicitly, since closedness now does not follow from being well-typed later. *)
  (** How do we represent subtyping in a later world? We have two distinct
      choices, because in Iris ▷(P ⇒ Q) ⊢ ▷ P ⇒ ▷ Q but not viceversa
      (unlike with raw step-indexing).
      In turn, that's because to show ▷ P ⇒ ▷ Q we can assume resources are
      valid one step earlier, unlike for ▷(P ⇒ Q).

      It seems easier, in subtyping judgment, to use the weaker choice: that is,
      just delay individual types via (Γ ⊨ TLater T <: TLater U), that is

      (□∀ v ρ, ⟦Γ⟧* ρ → ▷ ⟦T1⟧ ρ v → ▷ ⟦T2⟧ ρ v),

      instead of instead of introducing some notation to write

      (□∀ v ρ, ⟦Γ⟧* ρ → ▷ (⟦T1⟧ ρ v → ⟦T2⟧ ρ v)).

      And that forces using the same implication in the logical relation
      (unlike I did originally). *)
  Definition step_indexed_ivstp Γ T1 T2 i j: iProp Σ :=
    (□∀ ρ v, ⌜ nclosed_vl v 0 ⌝ → ⟦Γ⟧*ρ → (▷^i ⟦T1⟧ ρ v) → ▷^j ⟦T2⟧ ρ v)%I.
  Global Arguments step_indexed_ivstp /.

  Global Instance idtp_persistent Γ T d: Persistent (idtp Γ T d) := _.
  Global Instance idstp_persistent Γ T ds: Persistent (idstp Γ T ds) := _.
  Global Instance ietp_persistent Γ T e : Persistent (ietp Γ T e) := _.
  Global Instance step_indexed_ietp_persistent Γ T e i : Persistent (step_indexed_ietp Γ T e i) := _.
  Global Instance step_indexed_ivstp_persistent Γ T1 T2 i j : Persistent (step_indexed_ivstp Γ T1 T2 i j) := _.
  Global Instance ivstp_persistent Γ T1 T2 : Persistent (ivstp Γ T1 T2) := _.
End logrel.

Notation "d ↗ φ" := (idm_proj_semtype d φ) (at level 20).
Notation "⟦ T ⟧" := (interp T).
Notation "⟦ Γ ⟧*" := (interp_env Γ).
Notation "⟦ T ⟧ₑ" := (interp_expr (interp T)).

(** Single-definition typing *)
Notation "Γ ⊨d d : T" := (idtp Γ T d) (at level 64, d, T at next level).
(** Multi-definition typing *)
Notation "Γ ⊨ds ds : T" := (idstp Γ T ds) (at level 74, ds, T at next level).
(** Expression typing *)
Notation "Γ ⊨ e : T" := (ietp Γ T e) (at level 74, e, T at next level).
(** Indexed expression typing *)
Notation "Γ ⊨ e : T , i" := (step_indexed_ietp Γ T e i) (at level 74, e, T at next level).

Notation "Γ ⊨ T1 <: T2" := (ivstp Γ T1 T2) (at level 74, T1, T2 at next level).

Notation "Γ ⊨ [ T1 , i ]  <: [ T2 , j ]" := (step_indexed_ivstp Γ T1 T2 i j) (at level 74, T1, T2 at next level).
Notation "Γ ⊨ T1 , i  <: T2 , j" := (step_indexed_ivstp Γ T1 T2 i j) (at level 74, T1, T2 at next level).

(** Context extension for use with definition typing, as in
    [Γ |L V ⊨d d : T] and [Γ |L V ⊨ds ds : T]. *)
Notation "Γ |L V" := (defCtxCons Γ V) (at level 60).

Section logrel_lemmas.
  Context `{!dlangG Σ}.

  Lemma iterate_TLater_later i T ρ v:
    nclosed_vl v 0 →
    ⟦ iterate TLater i T ⟧ ρ v ≡ (▷^i ⟦ T ⟧ ρ v)%I.
  Proof.
    elim: i => [|i IHi] // => Hcl. rewrite iterate_S /= IHi //.
    iSplit; by [iIntros "#[_ $]" | iIntros "$"].
  Qed.

  Context Γ.

  Lemma semantic_typing_uniform_step_index T e i:
    Γ ⊨ e : T -∗ Γ ⊨ e : T,i.
  Proof.
    iIntros "[$ #H] !>" (ρ) "#HΓ".
    iInduction i as [|i] "IHi". by iApply "H".
    iApply wp_wand.
    iExact "IHi". naive_solver.
  Qed.

  Lemma interp_v_closed T w ρ: interp T ρ w -∗ ⌜ nclosed_vl w 0 ⌝.
  Proof.
    move: ρ; induction T => ρ /=;
      try by [iPureIntro | iIntros "[$ _]"];
      rewrite ?IHT1 ?IHT2 ?IHT; iPureIntro.
    all: by [intuition idtac | move => [n ->]].
  Qed.

  Lemma interp_env_len_agree ρ:
    ⟦ Γ ⟧* ρ -∗ ⌜ length ρ = length Γ ⌝.
  Proof.
    elim: Γ ρ => [|τ Γ' IHΓ] [|v ρ] //=; try by iPureIntro.
    rewrite IHΓ. by iIntros "[-> _] !%".
  Qed.

  Lemma interp_env_ρ_closed ρ: ⟦ Γ ⟧* ρ -∗ ⌜ cl_ρ ρ ⌝.
  Proof.
    elim: Γ ρ => [|τ Γ' IHΓ] [|v ρ] //=; try by iPureIntro.
    rewrite interp_v_closed IHΓ; iPureIntro => -[].
    by constructor.
  Qed.

  Lemma interp_env_props ρ:
    ⟦ Γ ⟧* ρ -∗ ⌜ cl_ρ ρ ∧ length ρ = length Γ ⌝.
  Proof.
    iIntros "#HG".
    iDestruct (interp_env_ρ_closed with "HG") as %?.
    iDestruct (interp_env_len_agree with "HG") as %?.
    by iPureIntro.
  Qed.

  Lemma Sub_Refl T i : Γ ⊨ [T, i] <: [T, i].
  Proof. by iIntros "/= !> **". Qed.

  Lemma Sub_Trans T1 T2 T3 i1 i2 i3 : Γ ⊨ [T1, i1] <: [T2, i2] -∗
                                      Γ ⊨ [T2, i2] <: [T3, i3] -∗
                                      Γ ⊨ [T1, i1] <: [T3, i3].
  Proof.
    iIntros "#Hsub1 #Hsub2 /= !> * % #Hg #HT".
    iApply ("Hsub2" with "[//] [//] (Hsub1 [//] [//] [//])").
  Qed.

End logrel_lemmas.
