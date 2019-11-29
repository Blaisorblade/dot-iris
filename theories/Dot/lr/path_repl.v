From iris.proofmode Require Import tactics.

From D Require Import iris_prelude.
From D Require lty olty_experiments.
From D.Dot.syn Require Import syn path_repl rules synLemmas.
From D.Dot.lr Require Import path_wp dlang_inst.
From D.Dot.lr Require unary_lr lr_lemma (* XXX *) lr_lemmasTSel.
From iris.program_logic Require Import ectx_language.
From D.pure_program_logic Require Import lifting.

Implicit Types
         (T : ty) (v w : vl) (t : tm) (d : dm) (ds : dms) (p q : path)
         (ρ : env) (l : label) (Pv : vl → Prop).

Section path_repl.
  Context `{dlangG Σ}.
  Implicit Types (φ: vl → iProp Σ).

  Notation path_wp p φ := (@path_wp Σ p φ).

  (* Not provable through pure props for impure [φ]. *)
  Lemma alias_paths_samepwp p q:
    alias_paths p q ↔
      (∃ u, path_wp_pure p (eq u)) ∧
      ∀ φ, path_wp p φ ≡ path_wp q φ.
  Proof.
    rewrite alias_paths_sameres; split.
    - destruct 1 as (v & Hp & Hq).
      split; first by [eauto]; intros φ.
      rewrite !path_wp_eq. f_equiv => w.
      do 2 f_equiv.
      split => Hr; [ rewrite -(path_wp_pure_det Hp Hr)
        | rewrite -(path_wp_pure_det Hq Hr)]; auto.
    - destruct 1 as ((u & Hp) & Heq). exists u; split; first done.
      (* Yes, very weird. *)
      apply (pure_soundness (M := iResUR Σ)).
      iRevert (Hp). by rewrite -!path_wp_pureable Heq.
  Qed.

  Lemma alias_paths_elim_eq φ {p q}:
    alias_paths p q →
    path_wp p φ ≡ path_wp q φ.
  Proof. intros ?%alias_paths_samepwp. intuition. Qed.

  (** Beware: we can do path replacement *before* substitution,
      even tho substitution and path replacement don't commute nicely.

      As a special case, we get the less surprising:
      [alias_paths_subst p r ids → path_wp q φ ≡ path_wp (q .p[p := r]) φ].

      But we do need the general form. *)
  Lemma path_replacement_equiv {p q ρ} p1 p2 (φ : vl → iProp Σ):
    p1 ~pp[ p := q ] p2 →
    alias_paths p.|[ρ] q.|[ρ] →
    path_wp p1.|[ρ] φ ≡ path_wp p2.|[ρ] φ.
  Proof.
    move => Hrepl.
    elim: Hrepl φ => [| p1' p2' l Hrepl IHrepl] φ /=.
    exact: alias_paths_elim_eq.
    apply IHrepl.
  Qed.

  Lemma alias_paths_simpl {p q} :
    path_wp_pure p (λ v, alias_paths q (pv v)) ↔
    alias_paths p q.
  Proof. apply alias_paths_symm. Qed.

  Definition alias_pathsI p q : iProp Σ := ⌜alias_paths p q⌝.

  Section with_unary_lr.
  Import unary_lr lr_lemma lr_lemmasTSel.
  Implicit Types (Γ : ctx).

  Lemma rewrite_path_path_repl {p q p1 p2 ρ v}:
    p1 ~pp[ p := q ] p2 →
    alias_paths p.|[ρ] q.|[ρ] → (* p : q.type *)
    ⌜alias_paths p1.|[ρ] (pv v)⌝%I ≡@{iProp Σ} ⌜alias_paths p2.|[ρ] (pv v)⌝%I.
    (* alias_paths p1.|[ρ] (pv v) ↔ alias_paths p2.|[ρ] (pv v). *)
  Proof.
    intros Hrew Hal.
    rewrite !alias_paths_pv_eq_1 -!path_wp_pureable.
    exact: path_replacement_equiv.
  Qed.

  Lemma rewrite_ty_path_repl {p q T1 T2 ρ v}:
    T1 ~Tp[ p := q ] T2 →
    alias_paths p.|[ρ] q.|[ρ] → (* p : q.type *)
    ⟦ T1 ⟧ ρ v ≡ ⟦ T2 ⟧ ρ v.
  Proof.
    move => Hrew; move: v ρ.
    induction Hrew => v ρ He /=; properness;
      by [ exact: path_replacement_equiv | exact: rewrite_path_path_repl
         | apply IHHrew; rewrite ?hsubst_comp | ].
  Qed.

  Lemma rewrite_ty_path_repl_rtc {p q T1 T2 ρ v}:
    T1 ~Tp[ p := q ]* T2 →
    alias_paths p.|[ρ] q.|[ρ] → (* p : q.type *)
    ⟦ T1 ⟧ ρ v ≡ ⟦ T2 ⟧ ρ v.
  Proof.
    move => Hr Hal.
    elim: Hr => [//|T {}T1 {}T2 Hr _ <-].
    apply (rewrite_ty_path_repl Hr Hal).
  Qed.

  Lemma ren_scons v ρ : ren (+1) >> v .: ρ = ρ.
  Proof. done. Qed.

  Lemma psubst_one_repl {T T' p v w ρ}:
    T .Tp[ p /]~ T' →
    alias_paths p.|[ρ] (pv v) →
    ⟦ T ⟧ (v .: ρ) w ≡ ⟦ T' ⟧ ρ w.
  Proof.
    intros Hrepl Hal.
    rewrite -(interp_weaken_one T' (v .: ρ) _) -(rewrite_ty_path_repl_rtc Hrepl)
      // hsubst_comp ren_scons /= alias_paths_symm //.
  Qed.

  Lemma singleton_aliasing Γ p q ρ i :
    Γ ⊨p p : TSing q, i -∗
    ⟦ Γ ⟧* ρ -∗ ▷^i alias_pathsI p.|[ρ] q.|[ρ].
  Proof.
    iIntros "#Hep #Hg". iSpecialize ("Hep" with "Hg").
    iNext i; iDestruct "Hep" as %Hep; iIntros "!%".
    by apply alias_paths_simpl.
  Qed.

  (** Non-pDOT rules start: *)

  Lemma singleton_self Γ T p i :
    Γ ⊨p p : T, i -∗
    Γ ⊨p p : TSing p, i.
  Proof.
    iIntros "#Hep !>" (ρ) "Hg". iSpecialize ("Hep" with "Hg"). iNext.
    iDestruct (path_wp_eq with "Hep") as (v Hpv) "_".
    iIntros "!%". by eapply alias_paths_simpl, alias_paths_self.
  Qed.

  Lemma singleton_self_sub Γ p T i :
    Γ ⊨p p : T, i -∗
    Γ ⊨ TSing p, i <: T, i.
  Proof.
    iIntros "#Hp !>" (ρ v) "Hg /= Heq".
    iSpecialize ("Hp" with "Hg"); iNext i.
    by iDestruct "Heq" as %->%(alias_paths_elim_eq (⟦ T ⟧ ρ)).
  Qed.

  Lemma singleton_sym_sub Γ p q T i:
    Γ ⊨p p : T, i -∗ (* Just to ensure [p] terminates and [TSing p] isn't empty. *)
    Γ ⊨ TSing p, i <: TSing q, i -∗
    Γ ⊨ TSing q, i <: TSing p, i.
  Proof.
    iIntros "#Hp #Hps !>" (ρ v) "#Hg /= Heq".
    iDestruct (path_wp_eq with "(Hp Hg)") as (w) "[Hpw _] {Hp}".
    iSpecialize ("Hps" $! _ w with "Hg Hpw"); iNext i; rewrite !alias_paths_pv_eq_1.
    iDestruct "Hps" as %Hqw; iDestruct "Hpw" as %Hpw; iDestruct "Heq" as %Hqv; iIntros "!%".
    by rewrite (path_wp_pure_det Hqv Hqw).
  Qed.

  (* Not too useful. *)
  (* Lemma singleton_self_skip Γ τ p i :
    Γ ⊨p p : T, 0 -∗
    Γ ⊨ iterate tskip i (path2tm p) : TSing p.
  Proof.
    rewrite singleton_self iptp2ietp.
    iIntros "Hp". iApply (T_Sub with "Hp").
    by iIntros "!> * _ $".
  Qed. *)

  Lemma singleton_self_inv Γ p q i :
    Γ ⊨p p : TSing q, i -∗
    Γ ⊨p q : TTop, i.
  Proof.
    iIntros "#Hpq !>" (ρ) "#Hg /=".
    iDestruct (singleton_aliasing with "Hpq Hg") as "Hal {Hpq Hg}".
    iNext i. iDestruct "Hal" as %(v & _ & Hqv)%alias_paths_sameres. iIntros "!%".
    by apply (path_wp_pure_wand Hqv).
  Qed.

  (* Not yet in the syntactic type system *)
  Lemma singleton_Mu_1 {Γ p T i T'} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : TMu T, i -∗
    Γ ⊨ TSing p, i <: T', i.
  Proof.
    iIntros "#Hp !>" (ρ v) "Hg /= Heq".
    iSpecialize ("Hp" with "Hg"); iNext i; iDestruct "Heq" as %Heq.
    by rewrite (alias_paths_elim_eq _ Heq) /= (psubst_one_repl Hrepl Heq).
  Qed.

  Lemma singleton_Mu_2 {Γ p T i T'} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : T', i -∗
    Γ ⊨ TSing p, i <: TMu T, i.
  Proof.
    iIntros "#Hp !>" (ρ v) "Hg /= Heq".
    iSpecialize ("Hp" with "Hg"); iNext i; iDestruct "Heq" as %Heq.
    by rewrite (alias_paths_elim_eq _ Heq) /= (psubst_one_repl Hrepl Heq).
  Qed.

  (** Non-pDOT rules end. *)

  Lemma Sub_singleton {Γ i p q T1 T2} (Hrepl : T1 ~Tp[ p := q ]* T2):
    Γ ⊨p p : TSing q, i -∗
    Γ ⊨ T1, i <: T2, i.
  Proof.
    iIntros "#Hal !>" (ρ v) "#Hg HT1". iSpecialize ("Hal" with "Hg"). iNext i.
    iDestruct "Hal" as %Hal%alias_paths_simpl.
    iApply (rewrite_ty_path_repl_rtc Hrepl Hal with "HT1").
  Qed.

  Lemma TMu_E_p' {Γ T T' p i} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : TMu T, i -∗ Γ ⊨p p : T', i.
  Proof.
    iIntros "#Hp"; rewrite -(plusnO i).
    iApply P_Sub; rewrite ?plusnO.
    iApply (singleton_self with "Hp").
    iApply (singleton_Mu_1 Hrepl with "Hp").
  Qed.

  Lemma TMu_E_p {Γ T T' p i} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : TMu T, i -∗ Γ ⊨p p : T', i.
  Proof.
    iIntros "#Hp !>" (ρ) "Hg /="; iSpecialize ("Hp" with "Hg"); iNext.
    rewrite !path_wp_eq.
    iDestruct "Hp" as (v Heq) "Hp"; iExists v; iFrame (Heq).
    by rewrite (psubst_one_repl Hrepl).
  Qed.

  Lemma TMu_I_p' {Γ T T' p i} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : T', i -∗ Γ ⊨p p : TMu T, i.
  Proof.
    iIntros "#Hp"; rewrite -(plusnO i).
    iApply P_Sub; rewrite ?plusnO.
    iApply (singleton_self with "Hp").
    iApply (singleton_Mu_2 Hrepl with "Hp").
  Qed.

  Lemma TMu_I_p {Γ T T' p i} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : T', i -∗ Γ ⊨p p : TMu T, i.
  Proof.
    iIntros "#Hp !>" (ρ) "Hg /="; iSpecialize ("Hp" with "Hg"); iNext.
    rewrite !path_wp_eq.
    iDestruct "Hp" as (v Heq) "Hp"; iExists v; iFrame (Heq).
    by rewrite (psubst_one_repl Hrepl).
  Qed.

  Lemma T_Forall_Ex_p Γ e1 p2 T1 T2 T2' (Hrepl : T2 .Tp[ p2 /]~ T2') :
    Γ ⊨ e1: TAll T1 T2 -∗
    Γ ⊨p p2 : T1, 0 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ ⊨ tapp e1 (path2tm p2) : T2'.
  Proof.
    iIntros "#He1 #Hp2 !>" (ρ) "#Hg /=".
    smart_wp_bind (AppLCtx _) v "#Hr {He1}" ("He1" with "Hg").
    iDestruct "Hr" as (t ->) "#HvFun".
    iDestruct (path_wp_eq with "(Hp2 Hg)") as (pw Hpwp) "{Hp2 Hg} Hpw".
    iDestruct (path_wp_to_wp _ (λ v, ⌜ pw = v ⌝)%I with "[%//]") as "Hpeq".
    iApply (wp_bind (fill [AppRCtx _])). rewrite path2tm_subst.
    iApply (wp_wand with "Hpeq"); iIntros (? <-) "/= {Hpeq}".
    rewrite -wp_pure_step_later; last done.
    iSpecialize ("HvFun" with "Hpw").
    iNext.
    iApply (wp_wand with "HvFun"); iIntros (v) "{HvFun Hpw} Hres".
    by rewrite (psubst_one_repl Hrepl).
  Qed.

  Lemma P_To_E Γ T p :
    Γ ⊨p p : T, 0 -∗ Γ ⊨ path2tm p : T.
  Proof.
    iIntros "#Hep !>" (ρ) "#Hg /="; rewrite path2tm_subst.
    by iApply (path_wp_to_wp with "(Hep Hg)").
  Qed.

  (* From pDOT *)
  Lemma PT_Mem_I Γ p T l i:
    Γ ⊨p pself p l : T, i -∗
    (*─────────────────────────*)
    Γ ⊨p p : TVMem l T, i.
  Proof.
    iIntros "#HE /= !>" (ρ) "#HG"; iSpecialize ("HE" with "HG"); iNext i.
    rewrite !path_wp_eq; iDestruct "HE" as (v Hpv w Hvw) "Htw {HG}".
    iExists _; iFrame (Hpv). eauto.
  Qed.

  Lemma iptp2ietp Γ T p :
    Γ ⊨p p : T, 0 -∗ Γ ⊨ path2tm p : T.
  Proof.
    iIntros "#Hep !>" (ρ) "#Hg /="; rewrite path2tm_subst.
    by iApply (path_wp_to_wp with "(Hep Hg)").
  Qed.

  Lemma singleton_trans Γ p q T i:
    Γ ⊨p p : TSing q, i -∗
    Γ ⊨p q : T, i -∗
    Γ ⊨p p : T, i.
  Proof.
    iIntros "#Hep #Heq !>" (ρ) "#Hg".
    iDestruct (singleton_aliasing with "Hep Hg") as "Hal1 {Hep}".
    iSpecialize ("Heq" with "Hg"). iNext i.
    by iDestruct "Hal1" as %->%(alias_paths_elim_eq _).
  Qed.

  Lemma singleton_elim Γ T p q l i:
    Γ ⊨p p : TSing q, i -∗
    Γ ⊨p pself q l : T, i -∗
    Γ ⊨p pself p l : TSing (pself q l), i.
  Proof.
    iIntros "#Hep #HqlT !>" (ρ) "#Hg".
    iSpecialize ("HqlT" with "Hg").
    iDestruct (singleton_aliasing with "Hep Hg") as "Hal {Hep Hg}".
    rewrite !path_wp_eq /=.
    iNext i. iDestruct "Hal" as %Hal. iDestruct "HqlT" as (vql Hql) "_".
    iIntros "!% /=". exists vql.
    rewrite (alias_paths_elim_eq_pure _ Hal). by split; apply Hql.
  Qed.
  End with_unary_lr.
End path_repl.

Module with_lty.
Section with_lty.
  Context `{dlangG Σ}.
  Implicit Types (φ: vl → iProp Σ).
  (** We don't have yet singleton types in the syntax: so add them as a semantic type
    and prove lemmas about them. Annoyingly, we can't talk about path replacement on
    semantic types. *)
  Import lty olty_experiments SemTypes.

  Lemma rewrite_ty_path_repl_tsel {p q p1 l p2 ρ v}:
    p1 ~pp[ p := q ] p2 →
    alias_paths p.|[ρ] q.|[ρ] → (* p : q.type *)
    oClose (oTSel p1 l) ρ v ≡ oClose (oTSel p2 l) ρ v.
  Proof. exact: path_replacement_equiv. Qed.
  Implicit Types (Γ : sCtx Σ) (τ : olty Σ 0).

  Definition oPsing p : olty Σ 0 :=
    olty0 (λ ρ v, alias_pathsI p.|[ρ] (pv v)).

  Lemma sem_psingleton_eq_1 p ρ v : oClose (oPsing p) ρ v ≡ ⌜ path_wp_pure p.|[ρ] (eq v) ⌝%I.
  Proof. done. Qed.

  Lemma sem_psingleton_eq_2 p ρ v : oClose (oPsing p) ρ v ≡ path_wp p.|[ρ] (λ w, ⌜ v = w ⌝ )%I.
  Proof. by rewrite sem_psingleton_eq_1 path_wp_pureable. Qed.

  Lemma singleton_aliasing Γ p q ρ i :
    Γ ⊨p p : oPsing q, i -∗
    ⟦ Γ ⟧* ρ -∗ ▷^i alias_pathsI p.|[ρ] q.|[ρ].
  Proof.
    iIntros "#Hep #Hg". iSpecialize ("Hep" with "Hg").
    iNext i; iDestruct "Hep" as %Hep; iIntros "!%".
    by apply alias_paths_simpl.
  Qed.

  Lemma singleton_self Γ τ p i :
    Γ ⊨p p : τ, i -∗
    Γ ⊨p p : oPsing p, i.
  Proof.
    iIntros "#Hep !>" (ρ) "Hg". iSpecialize ("Hep" with "Hg"). iNext.
    iDestruct (path_wp_eq with "Hep") as (v Hpv) "_".
    iIntros "!%". by eapply alias_paths_simpl, alias_paths_self.
  Qed.

  Lemma iptp2ietp Γ τ p :
    Γ ⊨p p : τ, 0 -∗ Γ ⊨ path2tm p : τ.
  Proof.
    iIntros "#Hep !>" (ρ) "#Hg /="; rewrite path2tm_subst.
    by iApply (path_wp_to_wp with "(Hep Hg)").
  Qed.

  Lemma T_Sub Γ e (T1 T2 : olty Σ 0) i:
    Γ ⊨ e : T1 -∗
    Γ ⊨ T1, 0 <: T2, i -∗
    (*───────────────────────────────*)
    Γ ⊨ iterate tskip i e : T2.
  Proof.
    iIntros "/= #HeT1 #Hsub !>" (ρ) "#Hg".
    rewrite tskip_subst -wp_bind.
    iApply (wp_wand with "(HeT1 Hg)").
    iIntros (v) "#HvT1".
    (* We can swap ▷^i with WP (tv v)! *)
    rewrite -wp_pure_step_later // -wp_value.
    by iApply "Hsub".
  Qed.

  (* XXX Generalize? *)
  Lemma singleton_self_skip Γ τ p i :
    Γ ⊨p p : τ, 0 -∗
    Γ ⊨ iterate tskip i (path2tm p) : oPsing p.
  Proof.
    rewrite singleton_self iptp2ietp.
    iIntros "Hp". iApply (T_Sub with "Hp").
    by iIntros "!> * _ $".
  Qed.

  Lemma singleton_sym Γ p q i:
    Γ ⊨p p : oPsing q, i -∗
    Γ ⊨p q : oPsing p, i.
  Proof.
    iIntros "#Hep !>" (ρ) "#Hg".
    iDestruct (singleton_aliasing with "Hep Hg") as "Hal". iNext i. iDestruct "Hal" as %Hal.
    iIntros "!%". by eapply alias_paths_simpl, alias_paths_symm.
  Qed.

  Lemma singleton_trans Γ p q r i:
    Γ ⊨p p : oPsing q, i -∗
    Γ ⊨p q : oPsing r, i -∗
    Γ ⊨p p : oPsing r, i.
  Proof.
    iIntros "#Hep #Heq !>" (ρ) "#Hg".
    iDestruct (singleton_aliasing with "Hep Hg") as "Hal1".
    iDestruct (singleton_aliasing with "Heq Hg") as "Hal2".
    iNext i. iDestruct "Hal1" as %Hal1. iDestruct "Hal2" as %Hal2.
    iIntros "!%". by eapply alias_paths_simpl, alias_paths_trans.
  Qed.

  Lemma singleton_elim Γ τ p q l i:
    Γ ⊨p p : oPsing q, i -∗
    Γ ⊨p pself q l : τ, i -∗
    Γ ⊨p pself p l : oPsing (pself q l), i.
  Proof.
    iIntros "#Hep #HqlT !>" (ρ) "#Hg".
    iDestruct (singleton_aliasing with "Hep Hg") as "Hal {Hep}".
    iSpecialize ("HqlT" with "Hg").
    rewrite !path_wp_eq /=.
    iNext i. iDestruct "Hal" as %Hal. iDestruct "HqlT" as (vql Hql) "_".
    iIntros "!% /=". exists vql.
    rewrite (alias_paths_elim_eq_pure _ Hal). auto.
  Qed.
  End with_lty.
End with_lty.
