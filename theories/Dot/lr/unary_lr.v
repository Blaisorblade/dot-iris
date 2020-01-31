(* From iris.proofmode Require Import tactics.
From D Require Import iris_prelude. *)
From D.Dot Require Export dlang_inst path_wp dot_lty.
(* From D.Dot Require Import lr_syn_aux. *)

(** Override notation from [dlang] to specify scope. *)
(* Notation "⟦ T ⟧" := (ty_interp T%ty). *)

(** Deduce types from variable names, like on paper, for readability and to help
    type inference for some overloaded operations (e.g. substitution). *)
Implicit Types
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (vs : vls) (ρ : var → vl).

Implicit Types (L T U : ty) (Γ : ctx).

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
  Implicit Types (interp φ : envD Σ) (ψ : D).

  (* Fixpoint def_interp_base (T : ty) : envPred dm Σ :=
    λ ρ d,
    match T with
    | TTMem _ L U => def_interp_tmem ⟦ L ⟧ ⟦ U ⟧ ρ d
    | TVMem _ T' => def_interp_vmem ⟦ T' ⟧ ρ d
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

  (** Definitions for semantic (definition) (sub)typing *)
  Definition idtp Γ T l d : iProp Σ :=
    □∀ ρ, ⌜path_includes (pv (ids 0)) ρ [(l, d)] ⌝ → ⟦Γ⟧* ρ → def_interp T l ρ d.|[ρ].
  Global Arguments idtp /.

  Definition idstp Γ T ds : iProp Σ :=
    ⌜wf_ds ds⌝ ∧ □∀ ρ, ⌜path_includes (pv (ids 0)) ρ ds ⌝ → ⟦Γ⟧* ρ → defs_interp T ρ ds.|[ρ].
  Global Arguments idstp /.

  Definition ietp Γ T e : iProp Σ :=
    □∀ ρ, ⟦Γ⟧* ρ → ⟦T⟧ₑ ρ (e.|[ρ]).
  Global Arguments ietp /. *)

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
  (* Definition istpi Γ T1 T2 i j: iProp Σ :=
    □∀ ρ v, ⟦Γ⟧* ρ → ▷^i ⟦T1⟧ ρ v → ▷^j ⟦T2⟧ ρ v.

  Global Arguments istpi /.

  Definition iptp Γ T p i: iProp Σ :=
    □∀ ρ, ⟦Γ⟧* ρ →
     ▷^i path_wp p.|[ρ] (λ v, ⟦T⟧ ρ v).
  Global Arguments iptp /.

  Local Notation IntoPersistent' P := (IntoPersistent false P P). *)

  (* Avoid auto-dropping box (and unfolding) when introducing judgments persistently. *)
  (* Global Instance idtp_persistent Γ T l d: IntoPersistent' (idtp Γ T l d) | 0 := _.
  Global Instance idstp_persistent Γ T ds: IntoPersistent' (idstp Γ T ds) | 0 := _.
  Global Instance ietp_persistent Γ T e : IntoPersistent' (ietp Γ T e) | 0 := _.
  Global Instance istpi_persistent Γ T1 T2 i j : IntoPersistent' (istpi Γ T1 T2 i j) | 0 := _.
  Global Instance iptp_persistent Γ T p i : IntoPersistent' (iptp Γ T p i) | 0 := _. *)
End logrel.

(* Notation "d ↗ ψ" := (dm_to_type d ψ) (at level 20). *)
(* Notation "⟦ T ⟧ₑ" := (interp_expr ⟦ T ⟧). *)

(*
(** Single-definition typing *)
Notation "Γ ⊨ {  l := d  } : T" := (idtp Γ T l d) (at level 74, d, l, T at next level).
(** Multi-definition typing *)
Notation "Γ ⊨ds ds : T" := (idstp Γ T ds) (at level 74, ds, T at next level).
(** Expression typing *)
Notation "Γ ⊨ e : T" := (ietp Γ T e) (at level 74, e, T at next level).

Notation "Γ ⊨p p : T , i" := (iptp Γ T p i) (at level 74, p, T, i at next level).

Notation "Γ ⊨ T1 , i <: T2 , j " := (istpi Γ T1 T2 i j) (at level 74, T1, T2, i, j at next level).

Import stamp_transfer.
(** Single-definition typing *)
Notation "Γ ⊨[ gφ  ] { l := d  } : T" := (wellMappedφ gφ → idtp Γ T l d)%I (at level 74, d, l, T at next level).
(** Multi-definition typing *)
Notation "Γ ⊨ds[ gφ  ] ds : T" := (wellMappedφ gφ → idstp Γ T ds)%I (at level 74, ds, T at next level).
(** Expression typing *)
Notation "Γ ⊨[ gφ  ] e : T" := (wellMappedφ gφ → ietp Γ T e)%I (at level 74, e, T at next level).
Notation "Γ ⊨p[ gφ  ] p : T , i" := (wellMappedφ gφ → iptp Γ T p i)%I (at level 74, p, T, i at next level).
Notation "Γ ⊨[ gφ  ] T1 , i <: T2 , j" := (wellMappedφ gφ → istpi Γ T1 T2 i j)%I (at level 74, T1, T2, i, j at next level).
*)

Section logrel_lemmas.
  Context `{!dlangG Σ}.

  (* Lemma iterate_TLater_later0 i T:
    ⟦ iterate TLater i T ⟧ ≡ (λ ρ v, ▷^i ⟦ T ⟧ ρ v)%I.
  Proof. move => ρ v. elim: i => [|i IHi] //. rewrite iterate_S /= IHi //. Qed.
  Lemma iterate_TLater_later i T ρ v:
    ⟦ iterate TLater i T ⟧ ρ v ≡ (▷^i ⟦ T ⟧ ρ v)%I.
  Proof. exact: iterate_TLater_later0. Qed. *)

  Context {Γ}.
End logrel_lemmas.
(*
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
Proof. apply adequate_safe, (adequacy_dot_sem _ e _ T), Hwp; naive_solver. Qed. *)
