From D Require Import iris_prelude asubst_base asubst_intf dlang.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting adequacy.
From D Require Import gen_iheap lty dlang ty_interp_subst_lemmas.

Implicit Types (Σ : gFunctors).

Set Suggest Proof Using.
Set Default Proof Using "Type".

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
