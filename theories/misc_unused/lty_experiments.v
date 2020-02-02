From D Require Import iris_prelude asubst_base asubst_intf dlang.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting adequacy.
From D Require Import gen_iheap saved_interp lty dlang ty_interp_subst_lemmas.

Implicit Types (Σ : gFunctors).

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
Program Definition subj_judgment_to_judgment {Σ s} : subj_judgment Σ s → judgment Σ :=
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
Program Definition nosubj_judgment_to_judgment {Σ} : nosubj_judgment Σ → judgment Σ := λ φ, φ.

Definition ivstp τ1 τ2 : nosubj_judgment Σ := (λ ρ, ∀ v, oClose τ1 ρ v → oClose τ2 ρ v)%I.
Program Definition sstpi τ1 i1 τ2 i2 := nosubj_judgment_to_judgment (Σ := Σ)
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
From D.Dot Require Import dlang_inst path_wp dot_lty.

From D.Dot.lr Require unary_lr path_repl.

Implicit Types
         (v: vl) (e: tm) (d: dm) (ds: dms) (p : path).

Module SemTypes2.

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

  Lemma singleton_aliasing Γ p q ρ i :
    Γ s⊨p p : oSing q, i -∗
    s⟦ Γ ⟧* ρ -∗ ▷^i alias_pathsI p.|[ρ] q.|[ρ].
  Proof.
    iIntros "#Hep #Hg". iSpecialize ("Hep" with "Hg").
    iNext i; iDestruct "Hep" as %Hep; iIntros "!%".
    by apply alias_paths_simpl.
  Qed.

  Lemma P_Sngl_Refl Γ τ p i :
    Γ s⊨p p : τ, i -∗
    Γ s⊨p p : oSing p, i.
  Proof.
    iIntros "#Hep !>" (ρ) "Hg". iSpecialize ("Hep" with "Hg"). iNext.
    iDestruct (path_wp_eq with "Hep") as (v Hpv) "_".
    iIntros "!%". by eapply alias_paths_simpl, alias_paths_self, alias_paths_pv_eq_1.
  Qed.

  Lemma sptp2setp Γ τ p :
    Γ s⊨p p : τ, 0 -∗ Γ s⊨ path2tm p : τ.
  Proof.
    iIntros "#Hep !>" (ρ) "#Hg /="; rewrite path2tm_subst.
    by iApply (path_wp_to_wp with "(Hep Hg)").
  Qed.

  Lemma T_Sub Γ e (T1 T2 : olty Σ 0) i:
    Γ s⊨ e : T1 -∗
    Γ s⊨ T1, 0 <: T2, i -∗
    (*───────────────────────────────*)
    Γ s⊨ iterate tskip i e : T2.
  Proof.
    iIntros "/= #HeT1 #Hsub !>" (ρ) "#Hg !>".
    rewrite tskip_subst -wp_bind.
    iApply (wp_wand with "(HeT1 Hg)").
    iIntros (v) "#HvT1".
    (* We can swap ▷^i with WP (tv v)! *)
    rewrite -wp_pure_step_later // -wp_value.
    by iApply "Hsub".
  Qed.

  (* XXX Generalize? *)
  Lemma singleton_self_skip Γ τ p i :
    Γ s⊨p p : τ, 0 -∗
    Γ s⊨ iterate tskip i (path2tm p) : oSing p.
  Proof.
    rewrite P_Sngl_Refl sptp2setp.
    iIntros "Hp". iApply (T_Sub with "Hp").
    by iIntros "!> * _ $".
  Qed.

  Lemma singleton_sym Γ p q i:
    Γ s⊨p p : oSing q, i -∗
    Γ s⊨p q : oSing p, i.
  Proof.
    iIntros "#Hep !>" (ρ) "#Hg".
    iDestruct (singleton_aliasing with "Hep Hg") as "Hal". iNext i. iDestruct "Hal" as %Hal.
    iIntros "!%". by eapply alias_paths_simpl, alias_paths_symm.
  Qed.

  Lemma P_Sngl_Trans Γ p q r i:
    Γ s⊨p p : oSing q, i -∗
    Γ s⊨p q : oSing r, i -∗
    Γ s⊨p p : oSing r, i.
  Proof.
    iIntros "#Hep #Heq !>" (ρ) "#Hg".
    iDestruct (singleton_aliasing with "Hep Hg") as "Hal1".
    iDestruct (singleton_aliasing with "Heq Hg") as "Hal2".
    iNext i. iDestruct "Hal1" as %Hal1. iDestruct "Hal2" as %Hal2.
    iIntros "!%". by eapply alias_paths_simpl, alias_paths_trans.
  Qed.

  Lemma P_Sngl_E Γ τ p q l i:
    Γ s⊨p p : oSing q, i -∗
    Γ s⊨p pself q l : τ, i -∗
    Γ s⊨p pself p l : oSing (pself q l), i.
  Proof.
    iIntros "#Hep #HqlT !>" (ρ) "#Hg".
    iDestruct (singleton_aliasing with "Hep Hg") as "Hal {Hep}".
    iSpecialize ("HqlT" with "Hg").
    rewrite !path_wp_eq /=.
    iNext i. iDestruct "Hal" as %Hal. iDestruct "HqlT" as (vql Hql) "_".
    iIntros "!% /="; setoid_rewrite alias_paths_pv_eq_1.
    by eapply alias_paths_sameres, alias_paths_pself.
  Qed.
  End with_lty.
End SemTypes2.
