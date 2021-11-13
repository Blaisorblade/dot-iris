(** * Semantic lemmas on singleton types, path typing and path replacement. *)
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_language.
From D.pure_program_logic Require Import lifting.
From D Require Import iris_prelude.
From D.Dot Require Import syn path_repl.
From D.Dot.lr Require Import path_wp unary_lr.
From D.Dot.semtyp_lemmas Require Import path_repl_lr.

Implicit Types
         (v w : vl) (t : tm) (d : dm) (ds : dms) (p q : path)
         (ρ : env) (l : label) (Pv : vl → Prop).

Set Suggest Proof Using.
Set Default Proof Using "Type".


Section path_repl.
  Context `{!dlangG Σ}.

  Lemma Sngl_pq_Stp {Γ i p q T1 T2} (Hrepl : T1 ~Tp[ p := q ]* T2) :
    Γ ⊨p p : TSing q, i -∗
    Γ ⊨ T1 <:[i] T2.
  Proof.
    iApply sSngl_pq_Stp; iApply sem_ty_path_repl_eq.
    apply fundamental_ty_path_repl_rtc, Hrepl.
  Qed.

  (** Lifting [sP_Mu_E] and [sP_Mu_I] is a bit less easy than other lemmas,
  because we need proof of [p]'s termination to relate semantic and syntactic
  substitution on types. *)
  Lemma P_Mu_E {Γ T T' p i} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : TMu T, i -∗ Γ ⊨p p : T', i.
  Proof.
    rewrite /iptp sP_Mu_E; iIntros ">#Hp !> %ρ Hg /=".
    iApply (strong_path_wp_wand with "(Hp Hg)"); iIntros "**".
    by rewrite (sem_psubst_one_eq Hrepl) ?alias_paths_pv_eq_1.
  Qed.

  Lemma P_Mu_I {Γ T T' p i} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : T', i -∗ Γ ⊨p p : TMu T, i.
  Proof.
    rewrite /iptp -sP_Mu_I; iIntros ">#Hp !> %ρ Hg /=".
    iApply (strong_path_wp_wand with "(Hp Hg)"); iIntros "**".
    by rewrite (sem_psubst_one_eq Hrepl) ?alias_paths_pv_eq_1.
  Qed.

  (** But these minor difficulties don't affect proofs of [P_Mu_E] and
  [P_Mu_I] from scratch; to wit: *)
  Lemma P_Mu_E' {Γ T T' p i} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : TMu T, i -∗ Γ ⊨p p : T', i.
  Proof.
    iIntros ">#Hp !> %ρ Hg /=".
    iApply (strong_path_wp_wand with "(Hp Hg)"); iIntros "**".
    by rewrite oMu_eq -(psubst_one_repl Hrepl) ?alias_paths_pv_eq_1.
  Qed.

  Lemma P_Mu_I' {Γ T T' p i} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : T', i -∗ Γ ⊨p p : TMu T, i.
  Proof.
    iIntros ">#Hp !> %ρ Hg /=".
    iApply (strong_path_wp_wand with "(Hp Hg)"); iIntros "**".
    by rewrite oMu_eq -(psubst_one_repl Hrepl) ?alias_paths_pv_eq_1.
  Qed.

  Lemma T_All_E_p Γ e1 p2 T1 T2 T2' (Hrepl : T2 .Tp[ p2 /]~ T2') :
    Γ ⊨ e1 : TAll T1 T2 -∗
    Γ ⊨p p2 : T1, 0 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ ⊨ tapp e1 (path2tm p2) : T2'.
  Proof.
    iIntros ">He1 >#Hp2".
    iDestruct (sT_All_E_p with "He1 Hp2") as ">Hep"; iIntros "!> %ρ #Hg".
    iDestruct (path_wp_eq with "(Hp2 Hg)") as (pw Hal%alias_paths_pv_eq_1) "_ /=".
    iApply (wp_wand with "(Hep Hg)"); iIntros "{Hg} %v #Hv".
    iApply (sem_psubst_one_eq Hrepl Hal with "Hv").
  Qed.
End path_repl.
