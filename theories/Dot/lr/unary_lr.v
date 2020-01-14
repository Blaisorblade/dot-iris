From iris.proofmode Require Import tactics.
From D Require Export iris_prelude.
From D Require Import ty_interp_subst_lemmas.
From D.Dot Require Export dlang_inst path_wp.

Include TyInterpLemmas VlSorts dlang_inst.

(** Deduce types from variable names, like on paper, for readability and to help
    type inference for some overloaded operations (e.g. substitution). *)
Implicit Types
         (L T U : ty) (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (Γ : ctx) (vs : vls) (ρ : var → vl).

(** The logical relation core is the [interp], interprets *open* types into
    predicates over *closed* values. Hence, [interp T ρ v] uses its argument [ρ]
    to interpret anything contained in T, but not things contained in v.

    Semantic judgements must apply instead to open terms/value/paths; therefore,
    they are defined using closing substitution on arguments of [interp].

    Similar comments apply to [def_interp].

    Additionally, both apply to *translated* arguments, hence they only expect
    [dtysem] and not [dtysyn] for type member definitions.
 *)

(* Use Program without its extended pattern-matching compiler; we only need
   its handling of coercions. *)
Unset Program Cases.

Definition label_of_ty T : option label :=
  match T with
  | TTMem l _ _ => Some l
  | TVMem l _ => Some l
  | _ => None
  end.

Section logrel.
  Context `{!dlangG Σ}.

  Notation D := (vl -d> iPropO Σ).
  Implicit Types (interp φ : envD Σ) (ψ : D).

  Definition def_interp_vmem interp : envPred dm Σ :=
    λ ρ d, (∃ vmem, ⌜d = dvl vmem⌝ ∧ interp ρ vmem)%I.
  Global Arguments def_interp_vmem /.

  Definition dm_to_type d ψ : iProp Σ :=
    ∃ s σ, ⌜ d = dtysem σ s ⌝ ∧ s ↗[ σ ] ψ.
  Notation "d ↗ ψ" := (dm_to_type d ψ) (at level 20).
  Global Instance dm_to_type_persistent d ψ: Persistent (d ↗ ψ) := _.

  Lemma dm_to_type_agree d ψ1 ψ2 v : d ↗ ψ1 -∗ d ↗ ψ2 -∗ ▷ (ψ1 v ≡ ψ2 v).
  Proof.
    iDestruct 1 as (s σ ?) "#Hs1".
    iDestruct 1 as (s' σ' ?) "#Hs2".
    simplify_eq. by iApply (stamp_σ_to_type_agree vnil with "Hs1 Hs2").
  Qed.

  Lemma dm_to_type_intro d s σ φ :
    d = dtysem σ s → s ↝ φ -∗ d ↗ φ (to_subst σ).
  Proof.
    iIntros. iExists s, σ. iFrame "%".
    by iApply stamp_σ_to_type_intro.
  Qed.

  Definition dm_to_type_eq d ψ : dm_to_type d ψ =
    (∃ s σ, ⌜ d = dtysem σ s ⌝ ∧ s ↗[ σ ] ψ)%I := eq_refl.
  Global Opaque dm_to_type.

  Definition def_interp_tmem interp1 interp2 : envPred dm Σ :=
    λ ρ d,
    (∃ ψ, (d ↗ ψ) ∧
       □ ((∀ v, ▷ interp1 ρ v → ▷ □ ψ v) ∧
          (∀ v, ▷ □ ψ v → ▷ interp2 ρ v)))%I.
  Global Arguments def_interp_tmem /.

  Definition lift_dinterp_vl l (dinterp: envPred dm Σ): envD Σ :=
    λ ρ v, (∃ d, ⌜v @ l ↘ d⌝ ∧ dinterp ρ d)%I.
  Global Arguments lift_dinterp_vl /.

  Definition interp_vmem l interp : envD Σ :=
    lift_dinterp_vl l (def_interp_vmem interp).
  Global Arguments interp_vmem /.

  Definition interp_tmem l interp1 interp2 : envD Σ :=
    lift_dinterp_vl l (def_interp_tmem interp1 interp2).
  Global Arguments interp_tmem /.

  Definition interp_expr interp : envPred tm Σ :=
    λ ρ t, (□ WP t {{ interp ρ }})%I.
  Global Arguments interp_expr /.

  Definition interp_and interp1 interp2 : envD Σ :=
    λ ρ v, (interp1 ρ v ∧ interp2 ρ v)%I.
  Global Arguments interp_and /.

  Definition interp_or interp1 interp2 : envD Σ :=
    λ ρ v, (interp1 ρ v ∨ interp2 ρ v)%I.
  Global Arguments interp_or /.

  Definition interp_later interp : envD Σ :=
    λ ρ v, (▷ interp ρ v)%I.
  Global Arguments interp_later /.

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

  Definition interp_prim b : envD Σ := λ ρ v, ⌜pure_interp_prim b v⌝%I.
  Global Arguments interp_prim /.

  Definition interp_top : envD Σ := λ ρ v, True%I.
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
    (∃ t, ⌜ v = vabs t ⌝ ∧
     □ ∀ w, ▷ interp1 ρ w → ▷ interp_expr interp2 (w .: ρ) t.|[w/])%I.
  Global Arguments interp_forall /.

  Definition interp_mu interp : envD Σ :=
    λ ρ v, interp (v .: ρ) v.
  Global Arguments interp_mu /.

  Definition interp_sel p (l: label) : envD Σ :=
    λ ρ v, (path_wp p.|[ρ]
      (λ vp, ∃ ψ d, ⌜vp @ l ↘ d⌝ ∧ d ↗ ψ ∧ ▷ □ ψ v))%I.
  Global Arguments interp_sel /.

  Definition interp_sing p : envD Σ :=
    λ ρ v, ⌜alias_paths p.|[ρ] (pv v)⌝%I.
  Global Arguments interp_sing /.

  Global Instance interp : TyInterp ty Σ := fix interp (T : ty) : envD Σ :=
    let _ := interp : TyInterp ty Σ in
    match T with
    | TTMem l L U => interp_tmem l (⟦ L ⟧) (⟦ U ⟧)
    | TVMem l T' => interp_vmem l (⟦ T' ⟧)
    | TAnd T1 T2 => interp_and (⟦ T1 ⟧) (⟦ T2 ⟧)
    | TOr T1 T2 => interp_or (⟦ T1 ⟧) (⟦ T2 ⟧)
    | TLater T => interp_later (⟦ T ⟧)
    | TPrim b => interp_prim b
    | TTop => interp_top
    | TBot => interp_bot
    | TAll T1 T2 => interp_forall (⟦ T1 ⟧) (⟦ T2 ⟧)
    | TMu T => interp_mu (⟦ T ⟧)
    | TSel p l => interp_sel p l
    | TSing p => interp_sing p
    end%I.

  Global Instance interp_lemmas: TyInterpLemmas ty Σ.
  Proof.
    split; induction T => sb1 sb2 w /=;
      properness; rewrite /= ?scons_up_swap ?hsubst_comp; trivial.
  Qed.

  Notation "⟦ T ⟧ₑ" := (interp_expr ⟦ T ⟧).

  Global Instance interp_persistent T ρ v :
    Persistent (⟦ T ⟧ ρ v).
  Proof. revert v ρ; induction T => w ρ /=; try apply _. Qed.

  Fixpoint def_interp_base (T : ty) : envPred dm Σ :=
    λ ρ d,
    match T with
    | TTMem _ L U => def_interp_tmem (⟦ L ⟧) (⟦ U ⟧) ρ d
    | TVMem _ T' => def_interp_vmem (⟦ T' ⟧) ρ d
    | _ => False
    end%I.

  Definition def_interp (T : ty) l : envPred dm Σ :=
    λ ρ d,
    (⌜ label_of_ty T = Some l ⌝ ∧ def_interp_base T ρ d)%I.

  Global Instance def_interp_base_persistent T ρ d :
    Persistent (def_interp_base T ρ d).
  Proof. destruct T; try apply _. Qed.

  Global Instance def_interp_persistent T l ρ d :
    Persistent (def_interp T l ρ d) := _.

  Definition defs_interp_and (interp1 interp2 : envPred dms Σ) : envPred dms Σ :=
    λ ρ ds, (interp1 ρ ds ∧ interp2 ρ ds)%I.

  Definition lift_dinterp_dms T : envPred dms Σ := λ ρ ds, (∃ l d,
    ⌜ dms_lookup l ds = Some d ⌝
    ∧ def_interp T l ρ d)%I.

  Fixpoint defs_interp T : envPred dms Σ :=
    match T with
    | TAnd T1 T2 => defs_interp_and (defs_interp T1) (defs_interp T2)
    | TTop => λ ρ ds, True
    | _ => lift_dinterp_dms T
    end%I.

  Global Instance defs_interp_persistent T ρ ds : Persistent (defs_interp T ρ ds).
  Proof. induction T; try apply _. Qed.

  Fixpoint interp_env (Γ : ctx) (ρ : var → vl) : iProp Σ :=
    match Γ with
    | T :: Γ' => interp_env Γ' (stail ρ) ∧ ⟦ T ⟧ ρ (shead ρ)
    | nil => True
    end%I.

  Notation "⟦ Γ ⟧*" := (interp_env Γ).

  Global Instance interp_env_persistent Γ ρ :
    Persistent (⟦ Γ ⟧* ρ).
  Proof. elim: Γ ρ => [|τ Γ IHΓ] ρ /=; apply _. Qed.

  Definition defCtxCons Γ V := TLater V :: Γ.

  (** Definitions for semantic (definition) (sub)typing *)
  Definition idtp Γ T l d : iProp Σ :=
    □∀ ρ, ⟦Γ⟧* ρ → def_interp T l ρ d.|[ρ].
  Global Arguments idtp /.

  Definition idstp Γ T ds : iProp Σ :=
    □∀ ρ, ⟦Γ⟧* ρ → defs_interp T ρ ds.|[ρ].
  Global Arguments idstp /.

  Definition ietp Γ T e : iProp Σ :=
    □∀ ρ, ⟦Γ⟧* ρ → ⟦T⟧ₑ ρ (e.|[ρ]).
  Global Arguments ietp /.

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
    □∀ ρ v, ⟦Γ⟧* ρ → ▷^i ⟦T1⟧ ρ v → ▷^j ⟦T2⟧ ρ v.

  Global Arguments step_indexed_ivstp /.

  Definition iptp Γ T p i: iProp Σ :=
    □∀ ρ, ⟦Γ⟧* ρ →
     ▷^i path_wp p.|[ρ] (λ v, ⟦T⟧ ρ v).
  Global Arguments iptp /.

  Local Notation IntoPersistent' P := (IntoPersistent false P P).

  (* Avoid auto-dropping box (and unfolding) when introducing judgments persistently. *)
  Global Instance idtp_persistent Γ T l d: IntoPersistent' (idtp Γ T l d) | 0 := _.
  Global Instance idstp_persistent Γ T ds: IntoPersistent' (idstp Γ T ds) | 0 := _.
  Global Instance ietp_persistent Γ T e : IntoPersistent' (ietp Γ T e) | 0 := _.
  Global Instance step_indexed_ivstp_persistent Γ T1 T2 i j : IntoPersistent' (step_indexed_ivstp Γ T1 T2 i j) | 0 := _.
  Global Instance iptp_persistent Γ T p i : IntoPersistent' (iptp Γ T p i) | 0 := _.
End logrel.

Notation "d ↗ ψ" := (dm_to_type d ψ) (at level 20).
Notation "⟦ Γ ⟧*" := (interp_env Γ).
Notation "⟦ T ⟧ₑ" := (interp_expr ⟦ T ⟧).

(** Single-definition typing *)
Notation "Γ ⊨ {  l := d  } : T" := (idtp Γ T l d) (at level 74, d, l, T at next level).
(** Multi-definition typing *)
Notation "Γ ⊨ds ds : T" := (idstp Γ T ds) (at level 74, ds, T at next level).
(** Expression typing *)
Notation "Γ ⊨ e : T" := (ietp Γ T e) (at level 74, e, T at next level).

Notation "Γ ⊨p p : T , i" := (iptp Γ T p i) (at level 74, p, T, i at next level).

Notation "Γ ⊨ T1 , i <: T2 , j " := (step_indexed_ivstp Γ T1 T2 i j) (at level 74, T1, T2, i, j at next level).

(** Context extension for use with definition typing, as in
    [Γ |L V ⊨d d : T] and [Γ |L V ⊨ds ds : T]. *)
Notation "Γ |L V" := (defCtxCons Γ V) (at level 60).

Import stamp_transfer.
(** Single-definition typing *)
Notation "Γ ⊨[ gφ  ] { l := d  } : T" := (wellMappedφ gφ → idtp Γ T l d)%I (at level 74, d, l, T at next level).
(** Multi-definition typing *)
Notation "Γ ⊨ds[ gφ  ] ds : T" := (wellMappedφ gφ → idstp Γ T ds)%I (at level 74, ds, T at next level).
(** Expression typing *)
Notation "Γ ⊨[ gφ  ] e : T" := (wellMappedφ gφ → ietp Γ T e)%I (at level 74, e, T at next level).
Notation "Γ ⊨p[ gφ  ] p : T , i" := (wellMappedφ gφ → iptp Γ T p i)%I (at level 74, p, T, i at next level).
Notation "Γ ⊨[ gφ  ] T1 , i <: T2 , j" := (wellMappedφ gφ → step_indexed_ivstp Γ T1 T2 i j)%I (at level 74, T1, T2, i, j at next level).

Section logrel_lemmas.
  Context `{!dlangG Σ}.

  Lemma iterate_TLater_later0 i T:
    ⟦ iterate TLater i T ⟧ ≡ (λ ρ v, ▷^i ⟦ T ⟧ ρ v)%I.
  Proof. move => ρ v. elim: i => [|i IHi] //. rewrite iterate_S /= IHi //. Qed.
  Lemma iterate_TLater_later i T ρ v:
    ⟦ iterate TLater i T ⟧ ρ v ≡ (▷^i ⟦ T ⟧ ρ v)%I.
  Proof. exact: iterate_TLater_later0. Qed.

  Lemma def_interp_tvmem_eq l T v ρ:
    def_interp (TVMem l T) l ρ (dvl v) ⊣⊢
    ⟦ T ⟧ ρ v.
  Proof.
    iSplit. by iDestruct 1 as (_ vmem [= ->]) "$".
    iIntros "H"; iSplit; first done; iExists v. by auto.
  Qed.

  Lemma interp_env_lookup Γ ρ T x:
    Γ !! x = Some T →
    ⟦ Γ ⟧* ρ -∗ ⟦ T.|[ren (+x)] ⟧ ρ (ρ x).
  Proof.
    elim: Γ ρ x => [//|τ' Γ' IHΓ] ρ x Hx /=.
    iDestruct 1 as "[Hg Hv]". move: x Hx => [ [->] | x Hx] /=.
    - rewrite hsubst_id. by [].
    - rewrite hrenS.
      iApply (interp_weaken_one (T.|[ren (+x)])).
      iApply (IHΓ (stail ρ) x Hx with "Hg").
  Qed.

  Context {Γ}.
  Lemma Sub_Refl T i : Γ ⊨ T, i <: T, i.
  Proof. by iIntros "!> **". Qed.

  Lemma Sub_Trans T1 T2 T3 i1 i2 i3 : Γ ⊨ T1, i1 <: T2, i2 -∗
                                      Γ ⊨ T2, i2 <: T3, i3 -∗
                                      Γ ⊨ T1, i1 <: T3, i3.
  Proof.
    iIntros "#Hsub1 #Hsub2 !> * #Hg #HT".
    iApply ("Hsub2" with "[//] (Hsub1 [//] [//])").
  Qed.

  Lemma Sub_Eq T U i j :
    Γ ⊨ T, i <: U, j ⊣⊢
    Γ ⊨ iterate TLater i T, 0 <: iterate TLater j U, 0.
  Proof. by cbn; setoid_rewrite iterate_TLater_later. Qed.
End logrel_lemmas.

From D Require Import swap_later_impl.
Import dlang_adequacy adequacy.

Theorem adequacy_dot_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} e Ψ T
  (Himpl : ∀ (Hdlang: dlangG Σ) v, ⟦ T ⟧ ids v -∗ ⌜Ψ v⌝)
  (Hlog : ∀ `{dlangG Σ} `(!SwapPropI Σ), allGs ∅ ==∗ [] ⊨ e : T):
  ∀ σ, adequate NotStuck e σ (λ v _, Ψ v).
Proof.
  eapply (adequacy_dlang _); [apply Himpl | iIntros (??) "Hgs"].
  iMod (Hlog with "Hgs") as "#Htyp".
  iEval rewrite -(hsubst_id e). iApply ("Htyp" $! ids with "[//]").
Qed.

Corollary safety_dot_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} e T
  (Hwp : ∀ `{dlangG Σ} `(!SwapPropI Σ), allGs ∅ ==∗ [] ⊨ e : T):
  safe e.
Proof. apply adequate_safe, (adequacy_dot_sem _ e _ T), Hwp; naive_solver. Qed.
