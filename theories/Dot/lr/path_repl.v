From iris.proofmode Require Import tactics.

From D Require Import iris_prelude.
From D.Dot.syn Require Import syn path_repl rules.
From D.Dot.lr Require Import path_wp dlang_inst unary_lr.
From iris.program_logic Require Import ectx_language.
From D.pure_program_logic Require Import lifting.

Implicit Types
         (T : ty) (v w : vl) (t : tm) (d : dm) (ds : dms) (p q : path)
         (ρ : env) (l : label) (Pv : vl → Prop).

Section path_repl.
  Context `{dlangG Σ}.
  Implicit Types (φ: vl → iProp Σ).

  Notation path_wp p φ := (@path_wp Σ p φ).

  Section with_unary_lr.
  Implicit Types (Γ : ctx).

  Lemma rewrite_ty_path_repl {p q T1 T2 ρ v}:
    T1 ~Tp[ p := q ] T2 →
    alias_paths p.|[ρ] q.|[ρ] → (* p : q.type *)
    p⟦ T1 ⟧ vnil ρ v ≡ p⟦ T2 ⟧ vnil ρ v.
  Proof.
    move => Hrew; move: v ρ.
    induction Hrew => v ρ He /=; properness;
      by [ exact: path_replacement_equiv | exact: rewrite_path_path_repl
         | apply IHHrew; rewrite ?hsubst_comp | | f_equiv => ?; exact: IHHrew].
  Qed.

  Lemma rewrite_ty_path_repl_rtc {p q T1 T2 ρ v}:
    T1 ~Tp[ p := q ]* T2 →
    alias_paths p.|[ρ] q.|[ρ] → (* p : q.type *)
    p⟦ T1 ⟧ vnil ρ v ≡ p⟦ T2 ⟧ vnil ρ v.
  Proof.
    move => Hr Hal.
    elim: Hr => [//|T {}T1 {}T2 Hr _ <-].
    apply (rewrite_ty_path_repl Hr Hal).
  Qed.

  Lemma psubst_one_repl {T T' p v w ρ}:
    T .Tp[ p /]~ T' →
    alias_paths p.|[ρ] (pv v) →
    p⟦ T ⟧ vnil (v .: ρ) w ≡ p⟦ T' ⟧ vnil ρ w.
  Proof.
    intros Hrepl Hal.
    rewrite -(persistent_ty_interp_lemmas.interp_weaken_one T' (v .: ρ) _) -(rewrite_ty_path_repl_rtc Hrepl)
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
    iIntros "!%". by eapply alias_paths_simpl, alias_paths_self, alias_paths_pv_eq_1.
  Qed.

  Lemma singleton_self_sub Γ p T i :
    Γ ⊨p p : T, i -∗
    Γ ⊨ TSing p, i <: T, i.
  Proof.
    iIntros "#Hp !>" (ρ v) "Hg /= Heq".
    iSpecialize ("Hp" with "Hg"); iNext i.
    iDestruct "Heq" as %->%(alias_paths_elim_eq (⟦ T ⟧ ρ)).
    by rewrite path_wp_pv.
  Qed.

  Lemma singleton_sym_sub Γ p q T i:
    Γ ⊨p p : T, i -∗ (* Just to ensure [p] terminates and [TSing p] isn't empty. *)
    Γ ⊨ TSing p, i <: TSing q, i -∗
    Γ ⊨ TSing q, i <: TSing p, i.
  Proof.
    iIntros "#Hp #Hps !>" (ρ v) "#Hg /= Heq".
    iDestruct (path_wp_eq with "(Hp Hg)") as (w) "[Hpw _] {Hp}".
    rewrite -alias_paths_pv_eq_1.
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

  (** Non-pDOT rules end. *)

  Lemma Sub_singleton {Γ i p q T1 T2} (Hrepl : T1 ~Tp[ p := q ]* T2):
    Γ ⊨p p : TSing q, i -∗
    Γ ⊨ T1, i <: T2, i.
  Proof.
    iIntros "#Hal !>" (ρ v) "#Hg HT1". iSpecialize ("Hal" with "Hg"). iNext i.
    iDestruct "Hal" as %Hal%alias_paths_simpl.
    iApply (rewrite_ty_path_repl_rtc Hrepl Hal with "HT1").
  Qed.

  Lemma TMu_E_p {Γ T T' p i} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : TMu T, i -∗ Γ ⊨p p : T', i.
  Proof.
    iIntros "#Hp !>" (ρ) "Hg /="; iSpecialize ("Hp" with "Hg"); iNext.
    rewrite !path_wp_eq.
    iDestruct "Hp" as (v Heq) "Hp"; iExists v; iFrame (Heq).
    by rewrite (psubst_one_repl Hrepl) ?alias_paths_pv_eq_1.
  Qed.

  Lemma TMu_I_p {Γ T T' p i} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : T', i -∗ Γ ⊨p p : TMu T, i.
  Proof.
    iIntros "#Hp !>" (ρ) "Hg /="; iSpecialize ("Hp" with "Hg"); iNext.
    rewrite !path_wp_eq.
    iDestruct "Hp" as (v Heq) "Hp"; iExists v; iFrame (Heq).
    by rewrite (psubst_one_repl Hrepl) ?alias_paths_pv_eq_1.
  Qed.

  (** For https://github.com/lampepfl/dotty/blob/85962b19ddf4f1909189bf07b40f9a05849f9bbf/compiler/src/dotty/tools/dotc/core/TypeComparer.scala#L553. *)
  Lemma singleton_Mu_dotty_approx_0 {Γ p i T1 T2} :
    iterate TLater i (TAnd T1 (TSing (shift p))) :: Γ ⊨ T1, i <: T2, i -∗
    Γ ⊨p p : TMu T1, i -∗
    Γ ⊨ TSing p, i <: TMu T2, i.
  Proof.
    (* iIntros "Hsub Hp".
    iApply singleton_self_sub.
    iApply (P_Sub' with "Hp").
    iApply Sub_Mu_X.
    (* We're stuck! *)
    Restart. *)
    iIntros "#Hsub #Hp !>" (ρ v) "#Hg /= #Heq".
    iSpecialize ("Hp" with "Hg").
    iAssert (▷^i ⟦ T1 ⟧ (v .: ρ) v)%I as "#HT1".
    by iNext i; iDestruct "Heq" as %Heq;
      rewrite (alias_paths_elim_eq _ Heq) path_wp_pv.
    iApply ("Hsub" $! (v .: ρ) v with "[$Hg] HT1").
    rewrite iterate_TLater_later /= hsubst_comp. iFrame "Heq HT1".
  Qed.

  (** What Dotty actually checks uses substitution twice. A simple case is the following: *)
  Lemma singleton_Mu_dotty_approx_1 {Γ p i T1 T2 T1' T2'}
    (Hrepl1 : T1 .Tp[ p /]~ T1') (Hrepl2 : T2 .Tp[ p /]~ T2'):
    Γ ⊨ T1', i <: T2', i -∗
    Γ ⊨p p : TMu T1, i -∗
    Γ ⊨ TSing p, i <: TMu T2, i.
  Proof.
    iIntros "#Hsub #Hp !>" (ρ v) "#Hg /= #Heq".
    iSpecialize ("Hp" with "Hg").
    iSpecialize ("Hsub" $! ρ v with "[#$Hg] [#]");
      iNext i; iDestruct "Heq" as %Heq;
      rewrite -(psubst_one_repl Hrepl1, psubst_one_repl Hrepl2) //
        (alias_paths_elim_eq _ Heq) path_wp_pv //.
  Qed.

  Lemma T_Forall_Ex_p Γ e1 p2 T1 T2 T2' (Hrepl : T2 .Tp[ p2 /]~ T2') :
    Γ ⊨ e1: TAll T1 T2 -∗
    Γ ⊨p p2 : T1, 0 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ ⊨ tapp e1 (path2tm p2) : T2'.
  Proof.
    iIntros "#He1 #Hp2 !>" (ρ) "#Hg /= !>".
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
    by rewrite (psubst_one_repl Hrepl) ?alias_paths_pv_eq_1.
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
    rewrite path_wp_pself !path_wp_eq;
      iDestruct "HE" as (v q Hlook Hpv) "Htw {HG} /=".
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
    by iDestruct "Hal1" as %->%(alias_paths_elim_eq (p⟦ _ ⟧ _ _)).
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
    iIntros "!% /="; setoid_rewrite alias_paths_pv_eq_1.
    by eapply alias_paths_sameres, alias_paths_pself.
  Qed.
  End with_unary_lr.
End path_repl.
