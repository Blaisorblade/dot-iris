From iris.proofmode Require Import tactics.
From D Require Export iris_prelude.
From D Require Import ty_interp_subst_lemmas.
From D.DSub Require Export operational.

Include TyInterpLemmas VlSorts operational.

(** Deduce types from variable names, like on paper, for readability and to help
    type inference for some overloaded operations (e.g. substitution). *)
Implicit Types
         (L T U : ty) (v : vl) (e : tm)
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

Section logrel.
  Context `{!dlangG Σ}.

  Notation D := (vl -d> iPropO Σ).
  Implicit Types (interp : envD Σ) (φ : D).

  (* XXX this is wrong unless we translate, and here I want for now to switch to having no translation.
     Tho maybe let's do one thing at a time. *)
  Definition dm_to_type v (ψ : D) : iProp Σ :=
    (∃ s σ, ⌜ v = vstamp σ s ⌝ ∧ s ↗[ σ ] ψ)%I.
  Notation "v ↗ φ" := (dm_to_type v φ) (at level 20).
  Global Instance dm_to_type_persistent d τ: Persistent (d ↗ τ) := _.
  Global Opaque dm_to_type.

  Definition interp_tmem interp1 interp2 : envD Σ :=
    λ ρ v,
    (∃ φ, (v ↗ φ) ∧
       □ ((∀ v, ▷ interp1 ρ v → ▷ □ φ v) ∧
          (∀ v, ▷ □ φ v → ▷ interp2 ρ v) ∧
          (∀ v, interp1 ρ v → interp2 ρ v)))%I.
  Global Arguments interp_tmem /.

  Definition interp_expr interp : (var -> vl) -d> tm -d> iPropO Σ :=
    λ ρ t, WP t {{ interp ρ }} %I.
  Global Arguments interp_expr /.

  Definition interp_nat : envD Σ := λ ρ v, (∃ n, ⌜v = vnat n⌝) %I.
  Global Arguments interp_nat /.

  Definition interp_top : envD Σ := λ ρ v, True%I.
  Global Arguments interp_top /.

  Definition interp_bot : envD Σ := λ ρ v, False%I.
  Global Arguments interp_bot /.

  (* XXX Paolo: This definition is correct but non-expansive, instead of
      contractive, unlike other logical relations here.
      It'd be good to write an example where this makes a difference.
      I think that would be something like
      nu x. { T = TNat; U = x.T -> x.T }:
      mu (x: {T <: TNat; U <: x.T -> TNat}).
      If the function type constructor is not contractive but only non-expansive,
      typechecking this example needs to establish x.T <: TNat having in context
      only x: {T <: TNat; U <: x.T -> TNat}.
    *)
  Definition interp_forall interp1 interp2 : envD Σ :=
    λ ρ v,
    (□ ∀ w, interp1 ρ w -∗ interp_expr interp2 (w .: ρ) (tapp (tv v) (tv w)))%I.
  Global Arguments interp_forall /.

  Definition interp_selA w interpL interpU : envD Σ :=
    λ ρ v,
    (interpU ρ v ∧ (interpL ρ v ∨
                    ∃ ϕ, w.[ρ] ↗ ϕ ∧ ▷ □ ϕ v))%I.
  Global Arguments interp_selA /.

  Definition interp_later interp : envD Σ :=
    λ ρ v, (▷ interp ρ v) % I.
  Global Arguments interp_later /.

  Definition interp_sel w : envD Σ :=
    interp_selA w interp_bot interp_top.
  Global Arguments interp_sel /.

  Global Instance interp : TyInterp ty Σ := fix interp (T : ty) : envD Σ :=
    let _ := interp : TyInterp ty Σ in
    match T with
    | TTop => interp_top
    | TBot => interp_bot
    | TLater T => interp_later (⟦ T ⟧)
    | TTMem L U => interp_tmem (⟦ L ⟧) (⟦ U ⟧)
    | TNat => interp_nat
    | TAll T1 T2 => interp_forall (⟦ T1 ⟧) (⟦ T2 ⟧)
    | TSel w => interp_sel w
    end % I.

  Global Instance interp_lemmas: TyInterpLemmas ty Σ.
  Proof.
    split; induction T => sb1 sb2 w /=;
      properness; rewrite /= ?scons_up_swap; trivial.
    autosubst.
  Qed.

  Notation "⟦ T ⟧ₑ" := (interp_expr ⟦ T ⟧).

  Global Instance interp_persistent T ρ v :
    Persistent (⟦ T ⟧ ρ v).
  Proof. revert v ρ; induction T => w ρ /=; try apply _. Qed.

  (* XXX here we needn't add a variable to the scope of its own type. But that won't hurt. *)
  Fixpoint interp_env (Γ : ctx) (ρ : var → vl) : iProp Σ :=
    match Γ with
    | T :: Γ' => interp_env Γ' (stail ρ) ∧ ⟦ T ⟧ ρ (shead ρ)
    | nil => True
    end%I.

  Notation "⟦ Γ ⟧*" := (interp_env Γ).

  Global Instance interp_env_persistent Γ ρ :
    Persistent (⟦ Γ ⟧* ρ).
  Proof. elim: Γ ρ => [|τ Γ IHΓ] ρ /=; apply _. Qed.

  Definition ietp Γ T e : iProp Σ :=
    (□∀ ρ, ⟦Γ⟧* ρ → ⟦T⟧ₑ ρ (e.|[ρ]))%I.
  Global Arguments ietp /.
  Notation "Γ ⊨ e : T" := (ietp Γ T e) (at level 74, e, T at next level).

  Definition step_indexed_ietp Γ T e i: iProp Σ :=
    (□∀ ρ, ⟦Γ⟧* ρ → ▷^i ⟦T⟧ₑ ρ (e.|[ρ]))%I.
  Global Arguments step_indexed_ietp /.
  Notation "Γ ⊨ e : T , i" := (step_indexed_ietp Γ T e i) (at level 74, e, T at next level).

  (** Indexed Subtyping. Defined on closed values. We must require closedness
      explicitly, since closedness now does not follow from being well-typed later. *)
  Definition step_indexed_ivstp Γ T1 T2 i j: iProp Σ :=
    (□∀ ρ v, ⟦Γ⟧* ρ → (▷^i ⟦T1⟧ ρ v) → ▷^j ⟦T2⟧ ρ v)%I.
  Global Arguments step_indexed_ivstp /.

  Global Instance ietp_persistent Γ T e : Persistent (ietp Γ T e) := _.
  Global Instance step_indexed_ietp_persistent Γ T e i : Persistent (step_indexed_ietp Γ T e i) := _.
  Global Instance step_indexed_ivstp_persistent Γ T1 T2 i j : Persistent (step_indexed_ivstp Γ T1 T2 i j) := _.
End logrel.

Notation "⟦ T ⟧ₑ" := (interp_expr ⟦ T ⟧).
Notation "⟦ Γ ⟧*" := (interp_env Γ).

(** Expression typing *)
Notation "Γ ⊨ e : T" := (ietp Γ T e) (at level 74, e, T at next level).
(** Indexed expression typing *)
Notation "Γ ⊨ e : T , i" := (step_indexed_ietp Γ T e i) (at level 74, e, T at next level).

Notation "Γ '⊨' '[' T1 ',' i ']' '<:' '[' T2 ',' j ']'" := (step_indexed_ivstp Γ T1 T2 i j) (at level 74, T1, T2 at next level).

Section logrel_lemmas.
  Context `{!dlangG Σ}.

  Lemma iterate_TLater_later i T ρ v:
    ⟦ iterate TLater i T ⟧ ρ v ≡ (▷^i ⟦ T ⟧ ρ v)%I.
  Proof.
    elim: i => [|i IHi] //.
    rewrite iterate_S /=; rewrite IHi //.
  Qed.

  Lemma semantic_typing_uniform_step_index Γ T e i:
    Γ ⊨ e : T -∗ Γ ⊨ e : T,i.
  Proof.
    iIntros "#H !>" (ρ) "#HΓ".
    iInduction i as [|i] "IHi". by iApply "H". iExact "IHi".
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
      iApply (IHΓ ((+1) >>> ρ) x Hx with "Hg").
  Qed.
End logrel_lemmas.
