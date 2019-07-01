From D Require Import iris_prelude asubst_base asubst_intf dlang.
From iris.program_logic Require Import language.
From D.pure_program_logic Require Import lifting adequacy.
From D Require Import gen_iheap saved_interp olty dlang.


(*
  - Redefining *existing judgments* on Olty will let us
    generalize current typing lemmas to be about semantic types.
    + However, we need to define substitution on semantic types.
      And figure out corresponding lemmas.
      Crucially, we must have (⟦ T ⟧).|[σ] ≡ ⟦ T.|[σ] ⟧.
      We might have already proven that, for to_subst.
  - Redefining judgments will let us... do what?
    Prove theorems about judgments? What is that good for?
    - Stating the lemmas without mentioning Γ?
    - Using common notation [Γ ⊨ J] for judgments?
    Neither seems so compelling.
  - What would be useful would be to prepare for HK-D<:
    while reusing as much as possible.
*)

Module Type OLty_judge (Import sorts: SortsIntf).
(* TODO Eventually switch to: *)

(* Include (LiftWp values sorts). *)
(* Or just inline this code there. *)
Include OLty sorts.

Class Closeable s := nclosed_s : s → nat → Prop.
Instance closeable_sort s `{Sort s} : Closeable s := nclosed.
Instance closeable_vl : Closeable vl := nclosed_vl.

Implicit Types (v: vl) (ρ vs : vls).
Implicit Types (Σ : gFunctors).

Definition test_interp_expr2 `{dlangG Σ} (φ : olty Σ) :=
  λ ρ t, WP t {{ φ ρ }} %I.

Section judgments.
Context `{dlangG Σ} `{OTyInterp ty Σ}.

Notation sCtx := (list (olty Σ)).
Notation ctx := (list ty).

Notation "⟦ T ⟧" := (oty_interp T).

Fixpoint env_oltyped (Γ : sCtx) ρ : iProp Σ :=
  match Γ, ρ with
  | φ :: Γ', v :: ρ => env_oltyped Γ' ρ ∗ φ (v::ρ) v
  | nil, nil => True
  | _, _ => False
  end%I.
Instance env_oltyped_persistent (Γ : sCtx) ρ: Persistent (env_oltyped Γ ρ).
Proof. elim: Γ ρ => [|τ Γ IHΓ] [|v ρ] /=; apply _. Qed.

Definition oty_interp_env (Γ : ctx) : sCtx := map oty_interp Γ.
Definition env_typed (Γ : ctx) : vls -d> iProp Σ := env_oltyped (oty_interp_env Γ).

Instance env_typed_persistent `{OTyInterp ty Σ} Γ ρ : Persistent (env_typed Γ ρ) := env_oltyped_persistent _ _.

Definition judgment Σ s : Type := option s * (vls -d> option s -d> iProp Σ).
Definition nosubj_judgment Σ : Type := vls -d> iProp Σ.
Definition subj_judgment Σ s : Type := s * (vls -d> s -d> iProp Σ).
Program Definition subj_judgment_to_judgment {Σ s} : subj_judgment Σ s → judgment Σ s :=
  λ '(x, φ), (Some x, λ ρ, from_option (φ ρ) False)%I.

Definition judgment_holds `{Closeable s} (Γ : sCtx) (J : judgment Σ s): iProp Σ :=
  (⌜ from_option (flip nclosed_s (length Γ)) True (fst J) ⌝ ∗ □∀ ρ, env_oltyped Γ ρ → (snd J) ρ (fst J))%I.
Notation "Γ ⊨ J" := (judgment_holds Γ J) (at level 74, J at next level).
Global Arguments judgment_holds /.

Program Definition ivtp (φ: olty Σ) v : judgment Σ vl := subj_judgment_to_judgment (v, φ).
Global Arguments ivtp /.

(* DOT/D<: judgments are indexed by [⋅]. *)
Notation "v v⋅: φ" := (ivtp φ v) (at level 73).
Definition judge_me Γ v φ := Γ ⊨ v v⋅: φ.

Definition interp_expr (φ : olty Σ) :=
  λ ρ t, WP t {{ φ ρ }} %I.
Global Arguments interp_expr /.
Definition tm := expr dlang_lang.
Context `{Closeable tm}.
Definition ittp (φ: olty Σ) t : judgment Σ tm := subj_judgment_to_judgment (t, interp_expr φ).
Global Arguments ittp /.

(* DOT/D<: judgments are indexed by [⋅]. *)
Notation "t t⋅: φ" := (ittp φ t) (at level 73).
Definition judge_me2 Γ t φ := Γ ⊨ t t⋅: φ.
(* Choosing vl is arbitrary. *)
Program Definition nosubj_judgment_to_judgment {Σ} : nosubj_judgment Σ → judgment Σ vl :=
  λ φ, (None, λ ρ _, φ ρ)%I.
Implicit Type (φ: olty Σ).

Definition ivstp φ1 φ2 : nosubj_judgment Σ := (λ ρ, ∀ v, ⌜ nclosed_vl v 0 ⌝ → φ1 ρ v → φ2 ρ v)%I.
Program Definition step_indexed_ivstp φ1 i1 φ2 i2 := nosubj_judgment_to_judgment (Σ := Σ)
  (λ ρ, ∀ v, ⌜ nclosed_vl v 0 ⌝ → (▷^i1 φ1 ρ v) → ▷^i2 φ2 ρ v)%I.
Notation "[ φ1 , i1 ] <: [ φ2 , i2 ]" := (step_indexed_ivstp φ1 i1 φ2 i2) (at level 73).
Lemma equiv_vstp Γ (φ1 φ2: olty Σ) i1 i2: (Γ ⊨ [φ1 , i1] <: [φ2 , i2]) ⊣⊢
    (□∀ ρ v, ⌜ nclosed_vl v 0 ⌝ → env_oltyped Γ ρ → (▷^i1 φ1 ρ v) → ▷^i2 φ2 ρ v)%I.
Proof.
  iSplit; [iIntros "#[_ H] /= !>" (???) "#?" |
    iIntros "#H"; iSplit; first done; iIntros "!>" (?) "#? /="; iIntros (??)].
  all: by iApply "H".
Qed.
Definition oAnd φ1 φ2 : olty Σ := Olty (λ ρ v, φ1 ρ v ∧ φ2 ρ v)%I.
Lemma andstp1 Γ φ1 φ2 i : (Γ ⊨ [oAnd φ1 φ2 , i] <: [φ1 , i]).
Proof.
  rewrite equiv_vstp /=. by iIntros "!>" (???) "#Hg #[? ?]".
Qed.
End judgments.

End OLty_judge.
