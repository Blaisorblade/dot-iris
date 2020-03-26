From D Require Import iris_prelude asubst_base asubst_intf dlang.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting adequacy.
From D Require Import gen_iheap lty dlang ty_interp_subst_lemmas.

Implicit Types (Σ : gFunctors).

Set Suggest Proof Using.
Set Default Proof Using "Type".

(*
  - Redefining *existing judgments* on Lty will let us
    generalize current typing lemmas to be about semantic types.
    + However, we need to define substitution on semantic types.
      And figure out corresponding lemmas.
      Crucially, we must have ⟦ T ⟧.|[σ] ≡ ⟦ T.|[σ] ⟧.
      We might have already proven that, for ∞.
  - Redefining judgments will let us... do what?
    Prove theorems about judgments? What is that good for?
    - Stating the lemmas without mentioning Γ?
    - Using common notation [Γ s⊨ J] for judgments?
    Neither seems so compelling.
  - What would be useful would be to prepare for HK-D<:
    while reusing as much as possible.
*)

Module Type Lty_judge (Import VS: VlSortsFullSig) (Import LVS : LiftWp VS).
Include Lty VS LVS.

Implicit Types (v: vl) (vs : vls) (ρ : env).

Section judgments.
Context `{dlangG Σ} `{OTyInterp ty Σ}.
Implicit Type (τ : olty Σ 0).

Notation ctx := (list (ty 0)).

Notation "⟦ T ⟧" := (oty_interp T).

Definition oty_interp_env (Γ : ctx) : sCtx Σ := map oty_interp Γ.
Definition env_typed (Γ : ctx) : env -d> iPropO Σ := env_oltyped (oty_interp_env Γ).

Global Instance env_typed_persistent' `{OTyInterp ty Σ} Γ ρ : Persistent (env_typed Γ ρ) :=
  env_oltyped_persistent _ _.

Definition judgment Σ : Type := env -d> iPropO Σ.
Definition nosubj_judgment Σ : Type := env -d> iPropO Σ.
Definition subj_judgment Σ s : Type := s * (env -d> s -d> iPropO Σ).
Definition subj_judgment_to_judgment {Σ s} : subj_judgment Σ s → judgment Σ :=
  λ '(x, φ) ρ, φ ρ x.

Definition judgment_holds (Γ : sCtx Σ) (J : judgment Σ): iProp Σ :=
  □∀ ρ, env_oltyped Γ ρ → J ρ.
Notation "Γ s⊨ J" := (judgment_holds Γ J) (at level 74, J at next level).
Global Arguments judgment_holds /.

Program Definition ivtp τ v : judgment Σ := subj_judgment_to_judgment (v, oClose τ).
Global Arguments ivtp /.

(* DOT/D<: judgments are indexed by [⋅]. *)
Notation "v v⋅: τ" := (ivtp τ v) (at level 73).
Local Definition test_judge_me Γ v τ := Γ s⊨ v v⋅: τ.

Definition setp τ t : judgment Σ := subj_judgment_to_judgment (t, interp_expr τ).
Global Arguments setp /.

(* DOT/D<: judgments are indexed by [⋅]. *)
Notation "t ⋅: τ" := (setp τ t) (at level 73).
Definition test_judge_me2 Γ t τ := Γ s⊨ t ⋅: τ.
Definition nosubj_judgment_to_judgment {Σ} : nosubj_judgment Σ → judgment Σ := λ φ, φ.

Definition ivstp τ1 τ2 : nosubj_judgment Σ := (λ ρ, ∀ v, oClose τ1 ρ v → oClose τ2 ρ v)%I.
Definition sstpi τ1 i1 τ2 i2 := nosubj_judgment_to_judgment (Σ := Σ)
  (λ ρ, ∀ v, ▷^i1 oClose τ1 ρ v → ▷^i2 oClose τ2 ρ v)%I.
Notation "τ1 , i1 <: τ2 , i2" := (sstpi τ1 i1 τ2 i2) (at level 73, τ2, i1, i2 at next level).

Lemma equiv_vstp Γ τ1 τ2 i1 i2: Γ s⊨ τ1 , i1 <: τ2 , i2 ⊣⊢
    (□∀ ρ v, env_oltyped Γ ρ → ▷^i1 oClose τ1 ρ v → ▷^i2 oClose τ2 ρ v)%I.
Proof.
  iSplit; [iIntros "#H /= !>" (??) "#Hg" |
    iIntros "#H !>" (?) "#Hg /="; iIntros (?)].
  all: iApply ("H" with "Hg").
Qed.

Lemma andstp1 Γ τ1 τ2 i : Γ s⊨ oAnd τ1 τ2 , i <: τ1 , i.
Proof.
  rewrite equiv_vstp /=. by iIntros "!>" (??) "#Hg #[? ?]".
Qed.
End judgments.

End Lty_judge.

From D.Dot Require Import syn lr_syn_aux syn.path_repl typeExtractionSyn.
From D.Dot Require Import dlang_inst path_wp unary_lr.

From D.Dot.lr Require unary_lr path_repl.

Implicit Types
         (v: vl) (e: tm) (d: dm) (ds: dms) (p : path).

Module SemTypes2.

(*
(** Indexed expression typing (not used for Dot). *)
Definition setpi `{dlangG Σ} e i Γ τ : iProp Σ :=
  □∀ ρ, s⟦Γ⟧* ρ → E⟦ eLater i τ ⟧ ρ (e.|[ρ]).
Global Arguments setpi /.

Notation "Γ s⊨ e : τ , i" := (setpi e i Γ τ) (at level 74, e, τ at next level).
*)

Section with_lty.
  Context `{dlangG Σ}.
  Import path_repl.
  Implicit Types (φ: vl → iProp Σ).

  Implicit Types (Γ : sCtx Σ) (T τ : oltyO Σ 0).

  Definition sem_path_repl_one T p T' : iProp Σ :=
    T' ≡ Olty (λI args ρ v, path_wp p (λ w, T args (w .: ρ) v)).
  Notation "T .sTp[ p /]~ T'" := (sem_path_repl_one T p T') (at level 65).

  (* Define semantic T1 ~sTp[ p := q ] T2 as
  alias_paths p.|[ρ] q.|[ρ] →
  ⟦ T1 ⟧ ρ v ≡ ⟦ T2 ⟧ ρ v.
  And relate the two versions of path_repl_one? *)

  (** We don't have yet singleton types in the syntax: so add them as a semantic type
    and prove lemmas about them. Annoyingly, we can't talk about path replacement on
    semantic types. *)
  Lemma psubst_one_repl_sem τ {p1 p2 p q ρ}:
    p1 ~pp[ p := q ] p2 →
    alias_paths p.|[ρ] q.|[ρ] → (* p : q.type *)
    path_wp p1.|[ρ] (oClose τ ρ) ≡ path_wp p2.|[ρ] (oClose τ ρ).
  Proof. apply: path_replacement_equiv. Qed.

  Lemma rewrite_ty_path_repl_tsel {p q p1 l p2 ρ v}:
    p1 ~pp[ p := q ] p2 →
    alias_paths p.|[ρ] q.|[ρ] → (* p : q.type *)
    oClose (oSel p1 l) ρ v ≡ oClose (oSel p2 l) ρ v.
  Proof. exact: path_replacement_equiv. Qed.

  Lemma sem_psingleton_eq_1 p ρ v : oClose (oSing p) ρ v ≡ ⌜ path_wp_pure p.|[ρ] (eq v) ⌝%I.
  Proof. by rewrite /=/alias_pathsI alias_paths_pv_eq_1. Qed.

  Lemma sem_psingleton_eq_2 p ρ v : oClose (oSing p) ρ v ≡ path_wp p.|[ρ] (λ w, ⌜ v = w ⌝ )%I.
  Proof. by rewrite sem_psingleton_eq_1 path_wp_pureable. Qed.

  (* Derivable syntactically. *)
  (* Lemma singleton_sym Γ p q i:
    Γ s⊨p p : oSing q, i -∗
    Γ s⊨p q : oSing p, i.
  Proof.
    iIntros "#Hep !>" (ρ) "#Hg".
    iDestruct (singleton_aliasing with "Hep Hg") as "Hal". iNext i. iDestruct "Hal" as %Hal.
    iIntros "!%". by eapply alias_paths_simpl, alias_paths_symm.
  Qed. *)
  End with_lty.
End SemTypes2.
