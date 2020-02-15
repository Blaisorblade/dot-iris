From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_language.
From D.pure_program_logic Require Import lifting.
From D Require Import iris_prelude.
From D.Dot.syn Require Import syn path_repl rules.
From D.Dot.lr Require Import path_wp dlang_inst unary_lr.

Implicit Types
         (v w : vl) (t : tm) (d : dm) (ds : dms) (p q : path)
         (ρ : env) (l : label) (Pv : vl → Prop).

Set Suggest Proof Using.
Set Default Proof Using "Type".

Section path_repl.
  Context `{dlangG Σ}.
  Implicit Types (φ: vl → iProp Σ).

  Notation path_wp p φ := (@path_wp Σ p φ).

  Lemma rewrite_ty_path_repl {p q T1 T2 args ρ v}:
    T1 ~Tp[ p := q ] T2 →
    alias_paths p.|[ρ] q.|[ρ] → (* p : q.type *)
    V⟦ T1 ⟧ args ρ v ≡ V⟦ T2 ⟧ args ρ v.
  Proof.
    move => Hrew; move: args ρ v.
    induction Hrew => args ρ v He /=; properness;
      try by [ exact: path_replacement_equiv | exact: rewrite_path_path_repl
         | apply IHHrew; rewrite ?hsubst_comp | | f_equiv => ?; exact: IHHrew].
  Qed.

  Lemma rewrite_ty_path_repl_rtc {p q T1 T2 args ρ v}:
    T1 ~Tp[ p := q ]* T2 →
    alias_paths p.|[ρ] q.|[ρ] → (* p : q.type *)
    V⟦ T1 ⟧ args ρ v ≡ V⟦ T2 ⟧ args ρ v.
  Proof.
    move => Hr Hal.
    elim: Hr => [//|T {}T1 {}T2 Hr _ <-].
    apply (rewrite_ty_path_repl Hr Hal).
  Qed.

  Lemma psubst_one_repl {T T' args p v w ρ}:
    T .Tp[ p /]~ T' →
    alias_paths p.|[ρ] (pv v) →
    V⟦ T ⟧ args (v .: ρ) w ≡ V⟦ T' ⟧ args ρ w.
  Proof.
    intros Hrepl Hal.
    rewrite -(interp_weaken_one T' (v .: ρ) _) -(rewrite_ty_path_repl_rtc Hrepl)
      // hsubst_comp ren_scons /= alias_paths_symm //.
  Qed.

  Lemma singleton_aliasing Γ p q ρ i :
    Γ s⊨p p : oSing q, i -∗
    s⟦ Γ ⟧* ρ -∗ ▷^i alias_pathsI p.|[ρ] q.|[ρ].
  Proof.
    iIntros "#Hep #Hg". iSpecialize ("Hep" with "Hg").
    iNext i; iDestruct "Hep" as %Hep; iIntros "!%".
    by apply alias_paths_simpl.
  Qed.

  (** Non-pDOT rules start: *)

  Lemma sP_Sngl_Refl Γ τ p i :
    Γ s⊨p p : τ, i -∗
    Γ s⊨p p : oSing p, i.
  Proof.
    iIntros "#Hep !>" (ρ) "Hg". iSpecialize ("Hep" with "Hg"). iNext.
    iDestruct (path_wp_eq with "Hep") as (v Hpv) "_".
    iIntros "!%". by eapply alias_paths_simpl, alias_paths_self, alias_paths_pv_eq_1.
  Qed.

  Lemma P_Sngl_Refl Γ T p i : Γ ⊨p p : T, i -∗ Γ ⊨p p : TSing p, i.
  Proof. apply sP_Sngl_Refl. Qed.

  Lemma sSngl_Self_Sub Γ p T i :
    Γ s⊨p p : T, i -∗
    Γ s⊨ oSing p, i <: T, i.
  Proof.
    iIntros "#Hp !>" (ρ v) "Hg /= Heq".
    iSpecialize ("Hp" with "Hg"); iNext i.
    iDestruct "Heq" as %->%(alias_paths_elim_eq (T _ ρ)).
    by rewrite path_wp_pv_eq.
  Qed.

  Lemma Sngl_Self_Sub Γ p T i : Γ ⊨p p : T, i -∗ Γ ⊨ TSing p, i <: T, i.
  Proof. apply sSngl_Self_Sub. Qed.

  Lemma sSngl_Sym_Sub Γ p q T i:
    Γ s⊨p p : T, i -∗ (* Just to ensure [p] terminates and [TSing p] isn't empty. *)
    Γ s⊨ oSing p, i <: oSing q, i -∗
    Γ s⊨ oSing q, i <: oSing p, i.
  Proof.
    iIntros "#Hp #Hps !>" (ρ v) "#Hg /= Heq".
    iDestruct (path_wp_eq with "(Hp Hg)") as (w) "[Hpw _] {Hp}".
    rewrite -alias_paths_pv_eq_1.
    iSpecialize ("Hps" $! _ w with "Hg Hpw"); iNext i; rewrite !alias_paths_pv_eq_1.
    iDestruct "Hps" as %Hqw; iDestruct "Hpw" as %Hpw; iDestruct "Heq" as %Hqv; iIntros "!%".
    by rewrite (path_wp_pure_det Hqv Hqw).
  Qed.

  Lemma Sngl_Sym_Sub Γ p q T i: Γ ⊨p p : T, i -∗
    Γ ⊨ TSing p, i <: TSing q, i -∗ Γ ⊨ TSing q, i <: TSing p, i.
  Proof. apply sSngl_Sym_Sub. Qed.

  Lemma sP_Sngl_Inv Γ p q i :
    Γ s⊨p p : oSing q, i -∗
    Γ s⊨p q : oTop, i.
  Proof.
    iIntros "#Hpq !>" (ρ) "#Hg /=".
    iDestruct (singleton_aliasing with "Hpq Hg") as "Hal {Hpq Hg}".
    iNext i. iDestruct "Hal" as %(v & _ & Hqv)%alias_paths_sameres. iIntros "!%".
    by apply (path_wp_pure_wand Hqv).
  Qed.

  Lemma P_Sngl_Inv Γ p q i : Γ ⊨p p : TSing q, i -∗ Γ ⊨p q : TTop, i.
  Proof. apply sP_Sngl_Inv. Qed.

  (** Non-pDOT rules end. *)

  Lemma Sngl_pq_Sub {Γ i p q T1 T2} (Hrepl : T1 ~Tp[ p := q ]* T2):
    Γ ⊨p p : TSing q, i -∗
    Γ ⊨ T1, i <: T2, i.
  Proof.
    iIntros "#Hal !>" (ρ v) "#Hg HT1". iSpecialize ("Hal" with "Hg"). iNext i.
    iDestruct "Hal" as %Hal%alias_paths_simpl.
    iApply (rewrite_ty_path_repl_rtc Hrepl Hal with "HT1").
  Qed.

  Lemma P_Mu_E {Γ T T' p i} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : TMu T, i -∗ Γ ⊨p p : T', i.
  Proof.
    iIntros "#Hp !>" (ρ) "Hg /="; iSpecialize ("Hp" with "Hg"); iNext.
    rewrite !path_wp_eq.
    iDestruct "Hp" as (v Heq) "Hp"; iExists v; iFrame (Heq).
    by rewrite (psubst_one_repl Hrepl) ?alias_paths_pv_eq_1.
  Qed.

  Lemma P_Mu_I {Γ T T' p i} (Hrepl : T .Tp[ p /]~ T') :
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
    iApply Sngl_Self_Sub.
    iApply (sP_Sub' with "Hp").
    iApply Sub_Mu_X.
    (* We're stuck! *)
    Restart. *)
    iIntros "#Hsub #Hp !>" (ρ v) "#Hg /= #Heq".
    iSpecialize ("Hp" with "Hg").
    iAssert (▷^i ⟦ T1 ⟧ (v .: ρ) v)%I as "#HT1".
    by iNext i; iDestruct "Heq" as %Heq;
      rewrite (alias_paths_elim_eq _ Heq) path_wp_pv_eq.
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
        (alias_paths_elim_eq _ Heq) path_wp_pv_eq //.
  Qed.

  Lemma T_All_Ex_p Γ e1 p2 T1 T2 T2' (Hrepl : T2 .Tp[ p2 /]~ T2') :
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

  Lemma sT_Path Γ τ p :
    Γ s⊨p p : τ, 0 -∗ Γ s⊨ path2tm p : τ.
  Proof.
    iIntros "#Hep !>" (ρ) "#Hg /="; rewrite path2tm_subst.
    by iApply (path_wp_to_wp with "(Hep Hg)").
  Qed.

  Lemma T_Path Γ T p :
    Γ ⊨p p : T, 0 -∗ Γ ⊨ path2tm p : T.
  Proof. apply sT_Path. Qed.

  (* From D.Dot Require Import lr_lemmas.
  (* Not too useful. *)
  (* XXX Generalize? *)
  Lemma s_singleton_self_skip Γ τ p i :
    Γ s⊨p p : τ, 0 -∗
    Γ s⊨ iterate tskip i (path2tm p) : oSing p.
  Proof.
    rewrite sP_Sngl_Refl sT_Path.
    iIntros "Hp". iApply (sT_Sub with "Hp").
    by iIntros "!> * _ $".
  Qed.

  Lemma singleton_self_skip Γ T p i :
    Γ ⊨p p : T, 0 -∗
    Γ ⊨ iterate tskip i (path2tm p) : TSing p.
  Proof. apply s_singleton_self_skip. Qed. *)

  (* From pDOT *)
  Lemma sP_Fld_I Γ p T l i:
    Γ ⊨p pself p l : T, i -∗
    (*─────────────────────────*)
    Γ ⊨p p : TVMem l T, i.
  Proof.
    iIntros "#HE /= !>" (ρ) "#HG"; iSpecialize ("HE" with "HG"); iNext i.
    rewrite path_wp_pself_eq !path_wp_eq;
      iDestruct "HE" as (v q Hlook Hpv) "Htw {HG} /=".
    iExists _; iFrame (Hpv). eauto.
  Qed.

  Lemma P_Fld_I Γ p T l i: Γ ⊨p pself p l : T, i -∗ Γ ⊨p p : TVMem l T, i.
  Proof. apply sP_Fld_I. Qed.

  Lemma sP_Sngl_Trans Γ p q T i:
    Γ s⊨p p : oSing q, i -∗
    Γ s⊨p q : T, i -∗
    Γ s⊨p p : T, i.
  Proof.
    iIntros "#Hep #Heq !>" (ρ) "#Hg".
    iDestruct (singleton_aliasing with "Hep Hg") as "Hal1 {Hep}".
    iSpecialize ("Heq" with "Hg"). iNext i.
    by iDestruct "Hal1" as %->%(alias_paths_elim_eq (T _ _)).
  Qed.

  Lemma P_Sngl_Trans Γ p q T i:
    Γ ⊨p p : TSing q, i -∗ Γ ⊨p q : T, i -∗ Γ ⊨p p : T, i.
  Proof. apply sP_Sngl_Trans. Qed.

  Lemma sP_Sngl_E Γ τ p q l i:
    Γ s⊨p p : oSing q, i -∗
    Γ s⊨p pself q l : τ, i -∗
    Γ s⊨p pself p l : oSing (pself q l), i.
  Proof.
    iIntros "#Hep #HqlT !>" (ρ) "#Hg".
    iSpecialize ("HqlT" with "Hg").
    iDestruct (singleton_aliasing with "Hep Hg") as "Hal {Hep Hg}".
    rewrite !path_wp_eq /=.
    iNext i. iDestruct "Hal" as %Hal. iDestruct "HqlT" as (vql Hql) "_".
    iIntros "!% /="; setoid_rewrite alias_paths_pv_eq_1.
    by eapply alias_paths_sameres, alias_paths_pself.
  Qed.

  Lemma P_Sngl_E Γ T p q l i: Γ ⊨p p : TSing q, i -∗ Γ ⊨p pself q l : T, i -∗
    Γ ⊨p pself p l : TSing (pself q l), i.
  Proof. apply sP_Sngl_E. Qed.
End path_repl.
