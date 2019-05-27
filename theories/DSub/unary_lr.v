From iris.proofmode Require Import tactics.
From D Require Export tactics iris_prelude.
From D.DSub Require Export operational.

(** Deduce types from variable names, like on paper, for readability and to help
    type inference for some overloaded operations (e.g. substitution). *)
Implicit Types
         (L T U: ty) (v: vl) (e: tm)
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
  Context `{!dsubG Σ}.

  (* Use Program without its extended pattern-matching compiler; we only need
     its handling of coercions. *)
  Unset Program Cases.

  Notation D := (vl -c> iProp Σ).
  Implicit Types (interp : envD Σ) (φ : D).

  (* XXX this is wrong unless we translate, and here I want for now to switch to having no translation.
     Tho maybe let's do one thing at a time. *)
  Definition idm_proj_semtype v (φ : D) : iProp Σ :=
    (∃ γ σ interp, ⌜ v = vstamp σ γ ⌝ ∗ γ ⤇ interp ∗ φ ≡ interp σ)%I.
  Global Arguments idm_proj_semtype /.
  Notation "v ↗ φ" := (idm_proj_semtype v φ) (at level 20).

  Definition interp_tmem interp1 interp2 : envD Σ :=
    λ ρ v,
    (⌜ nclosed_vl v 0 ⌝ ∗  ∃ φ, (v ↗ φ) ∗
       □ ((∀ v, ⌜ nclosed_vl v 0 ⌝ → ▷ interp1 ρ v → ▷ □ φ v) ∗
          (∀ v, ⌜ nclosed_vl v 0 ⌝ → ▷ □ φ v → ▷ interp2 ρ v) ∗
          (∀ v, interp1 ρ v → interp2 ρ v)))%I.
  Global Arguments interp_tmem /.

  Definition interp_expr interp : vls -c> tm -c> iProp Σ :=
    λ ρ t, WP t {{ interp ρ }} %I.
  Global Arguments interp_expr /.

  Definition interp_nat : envD Σ := λ ρ v, (∃ n, ⌜v = vnat n⌝) %I.
  Global Arguments interp_nat /.

  Definition interp_top : envD Σ := λ ρ v, ⌜ nclosed_vl v 0 ⌝%I.
  Global Arguments interp_top /.

  Definition interp_bot : envD Σ := λ ρ v, False%I.
  Global Arguments interp_bot /.

  (* XXX Paolo: This definition is correct but non-expansive; I suspect we might
      need to readd later here, but also to do the beta-reduction in place, to
      make it contractive (similarly to what's useful for equi-recursive types).
      However, I am not totally sure and might be wrong; it'd be good to
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
    (⌜ nclosed_vl v 0 ⌝ ∗ □ ∀ w, interp1 ρ w -∗ interp_expr interp2 (w :: ρ) (tapp (tv v) (tv w)))%I.
  Global Arguments interp_forall /.

  Definition interp_selA w interpL interpU : envD Σ :=
    λ ρ v,
    (interpU ρ v ∧ (interpL ρ v ∨
                    ∃ ϕ, w.[to_subst ρ] ↗ ϕ ∧ ▷ □ ϕ v))%I.
  Global Arguments interp_selA /.

  Definition interp_later interp : envD Σ :=
    λ ρ v, (⌜ nclosed_vl v 0 ⌝ ∗ ▷ interp ρ v) % I.
  Global Arguments interp_later /.

  Definition interp_sel w : envD Σ :=
    interp_selA w interp_bot interp_top.
  Global Arguments interp_sel /.

  Fixpoint interp (T: ty) : envD Σ :=
    match T with
    | TTop => interp_top
    | TBot => interp_bot
    | TLater T => interp_later (interp T)
    | TTMem L U => interp_tmem (interp L) (interp U)
    | TNat => interp_nat
    | TAll T1 T2 => interp_forall (interp T1) (interp T2)
    | TSel w => interp_sel w
  end % I.

  Global Instance dsubInterpΣ : dsubInterpG Σ := DsubInterpG _ interp.
  Notation "⟦ T ⟧" := (interp T).
  Notation "⟦ T ⟧ₑ" := (interp_expr (interp T)).

  Global Instance interp_persistent T ρ v :
    Persistent (⟦ T ⟧ ρ v).
  Proof. revert v ρ; induction T => w ρ; simpl; try apply _. Qed.

  (* XXX here we needn't add a variable to the scope of its own type. But that won't hurt. *)
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

  (* Really needed? Try to stop using it. *)
  Definition ivtp Γ T v : iProp Σ := (⌜ nclosed_vl v (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ → ⟦T⟧ ρ v.[to_subst ρ])%I.
  Global Arguments ivtp /.

  Definition ietp Γ T e : iProp Σ := (⌜ nclosed e (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ → ⟦T⟧ₑ ρ (e.|[to_subst ρ]))%I.
  Global Arguments ietp /.
  Notation "Γ ⊨ e : T" := (ietp Γ T e) (at level 74, e, T at next level).

  Lemma ietp_closed Γ T e: (Γ ⊨ e : T → ⌜ nclosed e (length Γ) ⌝)%I.
  Proof. iIntros "[$ _]". Qed.

  Definition step_indexed_ietp Γ T e i: iProp Σ :=
    (⌜ nclosed e (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ → ▷^i ⟦T⟧ₑ ρ (e.|[to_subst ρ]))%I.
  Global Arguments step_indexed_ietp /.
  Notation "Γ ⊨ e : T , i" := (step_indexed_ietp Γ T e i) (at level 74, e, T at next level).

  Lemma step_indexed_ietp_closed Γ T e i: (Γ ⊨ e : T, i → ⌜ nclosed e (length Γ) ⌝)%I.
  Proof. iIntros "[$ _]". Qed.

  (** Subtyping. Defined on values. *)
  Definition ivstp Γ T1 T2: iProp Σ := (□∀ ρ v, ⟦Γ⟧* ρ → ⟦T1⟧ ρ v → ⟦T2⟧ ρ v)%I.
  Global Arguments ivstp /.

  (** Indexed Subtyping. Defined on closed values. We must require closedness *)
(*       explicitly, since closedness now does not follow from being well-typed later. *)
  Definition step_indexed_ivstp Γ T1 T2 i j: iProp Σ :=
    (□∀ ρ v, ⌜ nclosed_vl v 0 ⌝ → ⟦Γ⟧*ρ → (▷^i ⟦T1⟧ ρ v) → ▷^j ⟦T2⟧ ρ v)%I.
  Global Arguments step_indexed_ivstp /.

  Global Instance ietp_persistent Γ T e : Persistent (ietp Γ T e) := _.
  Global Instance step_indexed_ietp_persistent Γ T e i : Persistent (step_indexed_ietp Γ T e i) := _.
  Global Instance step_indexed_ivstp_persistent Γ T1 T2 i j : Persistent (step_indexed_ivstp Γ T1 T2 i j) := _.
  Global Instance ivstp_persistent Γ T1 T2 : Persistent (ivstp Γ T1 T2) := _.
End logrel.

Notation "⟦ T ⟧" := (interp T).
Notation "⟦ Γ ⟧*" := (interp_env Γ).
Notation "⟦ T ⟧ₑ" := (interp_expr (interp T)).

(** Expression typing *)
Notation "Γ ⊨ e : T" := (ietp Γ T e) (at level 74, e, T at next level).
(** Indexed expression typing *)
Notation "Γ ⊨ e : T , i" := (step_indexed_ietp Γ T e i) (at level 74, e, T at next level).

Notation "Γ ⊨ T1 <: T2" := (ivstp Γ T1 T2) (at level 74, T1, T2 at next level).
Notation "Γ '⊨' '[' T1 ',' i ']' '<:' '[' T2 ',' j ']'" := (step_indexed_ivstp Γ T1 T2 i j) (at level 74, T1, T2 at next level).

Section logrel_lemmas.
  Context `{!dsubG Σ}.

  (* Lemma iterate_TLater_later i T ρ v: *)
  (*   nclosed_vl v 0 → *)
  (*   ⟦ iterate TLater i T ⟧ ρ v ≡ (▷^i ⟦ T ⟧ ρ v)%I. *)
  (* Proof. *)
  (*   elim: i => [|i IHi] // => Hcl. rewrite iterate_S /= IHi //. *)
  (*   iSplit; by [iIntros "#[_ $]" | iIntros "$"]. *)
  (* Qed. *)

  Context Γ.

  Lemma semantic_typing_uniform_step_index T e i:
    (Γ ⊨ e : T → Γ ⊨ e : T,i)%I.
  Proof.
    iIntros "[$ #H] !>" (ρ) "#HΓ".
    iInduction i as [|i] "IHi". by iApply "H". iApply "IHi".
  Qed.

  Lemma interp_v_closed T w ρ: (interp T ρ w → ⌜ nclosed_vl w 0 ⌝)%I.
  Proof.
    iInduction T as [] "IHT" forall (ρ w); iIntros "#HT //="; try by (iDestruct "HT" as "[% _]").
    - by iDestruct "HT" as (n) "->".
  Qed.

  Lemma interp_env_len_agree ρ:
    (⟦ Γ ⟧* ρ → ⌜ length ρ = length Γ ⌝)%I.
  Proof.
    iInduction Γ as [|τ Γ'] "IHΓ" forall (ρ); destruct ρ => //=.
    iIntros "#[HG Hv]".
    by iDestruct ("IHΓ" $! ρ with "HG") as "->".
  Qed.

  Lemma interp_env_ρ_closed ρ: (⟦ Γ ⟧* ρ → ⌜ cl_ρ ρ ⌝)%I.
  Proof.
    iInduction Γ as [|τ Γ'] "IHΓ" forall (ρ); destruct ρ => //=.
    iIntros "[#HG #HT]".
    iDestruct (interp_v_closed with "HT") as %?.
    iDestruct ("IHΓ" with "HG") as %?.
    iPureIntro; by constructor.
  Qed.

End logrel_lemmas.
