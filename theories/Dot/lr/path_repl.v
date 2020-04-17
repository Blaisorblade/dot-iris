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

Definition opSubst {Σ n} p (T : oltyO Σ n) : oltyO Σ n :=
  Olty (λI args ρ v, path_wp p.|[ρ] (λ w, T args (w .: ρ) v)).
Notation "T .sTp[ p /]" := (opSubst p T) (at level 65).

(* sem_psubst_ty  *)
Definition sem_ty_path_repl {Σ n} p q (T1 T2 : olty Σ n) : Prop :=
  ∀ args ρ v, alias_paths p.|[ρ] q.|[ρ] → T1 args ρ v ≡ T2 args ρ v.
Notation "T1 ~sTp[ p := q  ]* T2" :=
  (sem_ty_path_repl p q T1 T2) (at level 70).

Section path_repl.
  Context `{!dlangG Σ}.
  Implicit Types (φ: vl → iProp Σ).

  Notation path_wp p φ := (@path_wp Σ p φ).

  Lemma opSubst_pv_eq {n} v (T : oltyO Σ n) : T .sTp[ pv v /] ≡ T.|[v/].
  Proof. move=> args ρ w /=. by rewrite path_wp_pv_eq subst_swap_base. Qed.

  Lemma sem_psubst_one_repl {n} {T : olty Σ n} {args p v w ρ}:
    alias_paths p.|[ρ] (pv v) →
    T .sTp[ p /] args ρ w ≡ T args (v .: ρ) w.
  Proof. move=> /alias_paths_elim_eq /= ->. by rewrite path_wp_pv_eq. Qed.

  Lemma fundamental_ty_path_repl {p q T1 T2}
    (Hrew : T1 ~Tp[ p := q ] T2) :
    V⟦ T1 ⟧ ~sTp[ p := q ]* V⟦ T2 ⟧.
  Proof.
    rewrite /sem_ty_path_repl; induction Hrew => args ρ v He /=; properness;
      try by [ exact: path_replacement_equiv | exact: rewrite_path_path_repl
         | apply IHHrew; rewrite ?hsubst_comp | | f_equiv => ?; exact: IHHrew].
  Qed.

  Lemma fundamental_ty_path_repl_rtc {p q T1 T2}
    (Hrew : T1 ~Tp[ p := q ]* T2) :
    V⟦ T1 ⟧ ~sTp[ p := q ]* V⟦ T2 ⟧.
  Proof.
    move=> args ρ v Hal. elim: Hrew => [//|T {}T1 {}T2 Hr _ <-].
    apply (fundamental_ty_path_repl Hr), Hal.
  Qed.

  Lemma rewrite_ty_path_repl_rtc {p q T1 T2 args ρ}
    (Hrepl : T1 ~Tp[ p := q ]* T2):
    alias_paths p.|[ρ] q.|[ρ] → (* p : q.type *)
    V⟦ T1 ⟧ args ρ ≡ V⟦ T2 ⟧ args ρ.
  Proof. intros Hal v. apply: (fundamental_ty_path_repl_rtc Hrepl) Hal. Qed.

  Lemma sem_psubst_one_eq {T T' args p v ρ}
    (Hrepl : T .Tp[ p /]~ T')
    (Hal : alias_paths p.|[ρ] (pv v)) :
    V⟦ T' ⟧ args ρ ≡ (V⟦ T ⟧) .sTp[ p /] args ρ.
  Proof.
    rewrite -(interp_weaken_one T' (v .: ρ)) => w.
    rewrite -(rewrite_ty_path_repl_rtc Hrepl) /=.
    by rewrite (alias_paths_elim_eq _ Hal) path_wp_pv_eq.
    by rewrite hsubst_comp ren_scons /= alias_paths_symm.
  Qed.

  Lemma psubst_one_repl {T T' args p v w ρ}
    (Hr : T .Tp[ p /]~ T') (Hal : alias_paths p.|[ρ] (pv v)) :
    V⟦ T ⟧ args (v .: ρ) w ≡ V⟦ T' ⟧ args ρ w.
  Proof. by rewrite (sem_psubst_one_eq Hr Hal) (sem_psubst_one_repl Hal). Qed.

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
    iApply (strong_path_wp_wand with "[] Hep"); iIntros (v Hpv) "!> _ !%".
    apply alias_paths_pv_eq_1, Hpv.
  Qed.

  Lemma P_Sngl_Refl Γ T p i : Γ ⊨p p : T, i -∗ Γ ⊨p p : TSing p, i.
  Proof. apply sP_Sngl_Refl. Qed.

  Lemma sSngl_Sub_Self Γ p T i :
    Γ s⊨p p : T, i -∗
    Γ s⊨ oSing p, i <: T, i.
  Proof.
    iIntros "#Hp !>" (ρ v) "Hg /= Heq".
    iSpecialize ("Hp" with "Hg"); iNext i.
    iDestruct "Heq" as %->%(alias_paths_elim_eq (T _ ρ)).
    by rewrite path_wp_pv_eq.
  Qed.

  Lemma Sngl_Sub_Self Γ p T i : Γ ⊨p p : T, i -∗ Γ ⊨ TSing p, i <: T, i.
  Proof. apply sSngl_Sub_Self. Qed.

  Lemma sSngl_Sub_Sym Γ p q T i:
    Γ s⊨p p : T, i -∗ (* Just to ensure [p] terminates and [oSing p] isn't empty. *)
    Γ s⊨ oSing p, i <: oSing q, i -∗
    Γ s⊨ oSing q, i <: oSing p, i.
  Proof.
    iIntros "#Hp #Hps !>" (ρ v) "#Hg /= Heq".
    iDestruct (path_wp_eq with "(Hp Hg)") as (w) "[Hpw _] {Hp}".
    rewrite -alias_paths_pv_eq_1; iSpecialize ("Hps" $! _ w with "Hg Hpw");
      rewrite !alias_paths_pv_eq_1.
    iNext i; iRevert "Hps Hpw Heq"; iIntros "!%" (Hqw Hpw Hqv).
    by rewrite (path_wp_pure_det Hqv Hqw).
  Qed.

  Lemma Sngl_Sub_Sym Γ p q T i: Γ ⊨p p : T, i -∗
    Γ ⊨ TSing p, i <: TSing q, i -∗ Γ ⊨ TSing q, i <: TSing p, i.
  Proof. apply sSngl_Sub_Sym. Qed.

  Lemma sP_Sngl_Inv Γ p q i :
    Γ s⊨p p : oSing q, i -∗
    Γ s⊨p q : oTop, i.
  Proof.
    iIntros "#Hpq !>" (ρ) "#Hg /=".
    iDestruct (singleton_aliasing with "Hpq Hg") as "Hal {Hpq Hg}".
    iNext i. iDestruct "Hal" as %(v & _ & Hqv)%alias_paths_sameres. iIntros "!%".
    exact: (path_wp_pure_wand Hqv).
  Qed.

  Lemma P_Sngl_Inv Γ p q i : Γ ⊨p p : TSing q, i -∗ Γ ⊨p q : TTop, i.
  Proof. apply sP_Sngl_Inv. Qed.

  (** Non-pDOT rules end. *)

  (** Obtain this rule for *semantic* substitution. *)
  Lemma sSngl_pq_Sub {Γ i p q T1 T2} (Hrepl : T1 ~sTp[ p := q ]* T2) :
    Γ s⊨p p : oSing q, i -∗
    Γ s⊨ T1, i <: T2, i.
  Proof.
    iIntros "#Hal !>" (ρ v) "#Hg HT1". iSpecialize ("Hal" with "Hg"). iNext i.
    iDestruct "Hal" as %Hal%alias_paths_simpl.
    iApply (Hrepl with "HT1"). exact Hal.
  Qed.

  Lemma Sngl_pq_Sub {Γ i p q T1 T2} (Hrepl : T1 ~Tp[ p := q ]* T2):
    Γ ⊨p p : TSing q, i -∗
    Γ ⊨ T1, i <: T2, i.
  Proof. apply sSngl_pq_Sub, fundamental_ty_path_repl_rtc, Hrepl. Qed.

  Lemma sP_Mu_E {Γ T p i} :
    Γ s⊨p p : oMu T, i -∗ Γ s⊨p p : T .sTp[ p /], i.
  Proof.
    iIntros "#Hp !>" (ρ) "Hg /=".
    iApply (strong_path_wp_wand with "[] (Hp Hg)"); iIntros "!> **".
    by rewrite oMu_eq sem_psubst_one_repl ?alias_paths_pv_eq_1.
  Qed.

  Lemma P_Mu_E {Γ T T' p i} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : TMu T, i -∗ Γ ⊨p p : T', i.
  Proof.
    (* Proof from scratch *)
    (* iIntros "#Hp !>" (ρ) "Hg /=".
    iApply (strong_path_wp_wand with "[] (Hp Hg)"); iIntros "!> **".
    by rewrite oMu_eq -(psubst_one_repl Hrepl ) ?alias_paths_pv_eq_1. *)
    (* Even if we reuse sP_Mu_E, we must prove that [p] terminates. *)
    rewrite /iptp sP_Mu_E; iIntros "#Hp !>" (ρ) "Hg /=".
    iApply (strong_path_wp_wand with "[] (Hp Hg)"); iIntros "!> **".
    by rewrite (sem_psubst_one_eq Hrepl) ?alias_paths_pv_eq_1.
  Qed.

  Lemma sP_Mu_I {Γ T p i} :
    Γ s⊨p p : T .sTp[ p /], i -∗ Γ s⊨p p : oMu T, i.
  Proof.
    iIntros "#Hp !>" (ρ) "Hg /=".
    iApply (strong_path_wp_wand with "[] (Hp Hg)"); iIntros "!> **".
    by rewrite oMu_eq sem_psubst_one_repl ?alias_paths_pv_eq_1.
  Qed.

  Lemma P_Mu_I {Γ T T' p i} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : T', i -∗ Γ ⊨p p : TMu T, i.
  Proof.
    (* iIntros "#Hp !>" (ρ) "Hg /=".
    iApply (strong_path_wp_wand with "[] (Hp Hg)"); iIntros "!> **".
    by rewrite oMu_eq (psubst_one_repl Hrepl) ?alias_paths_pv_eq_1. *)
    rewrite /iptp -sP_Mu_I; iIntros "#Hp !>" (ρ) "Hg /=".
    iApply (strong_path_wp_wand with "[] (Hp Hg)"); iIntros "!> **".
    by rewrite (sem_psubst_one_eq Hrepl) ?alias_paths_pv_eq_1.
  Qed.

  (** For https://github.com/lampepfl/dotty/blob/85962b19ddf4f1909189bf07b40f9a05849f9bbf/compiler/src/dotty/tools/dotc/core/TypeComparer.scala#L553. *)
  Lemma singleton_Mu_dotty_approx_0 {Γ p i T1 T2} :
    iterate TLater i (TAnd T1 (TSing (shift p))) :: Γ ⊨ T1, i <: T2, i -∗
    Γ ⊨p p : TMu T1, i -∗
    Γ ⊨ TSing p, i <: TMu T2, i.
  Proof.
    (* iIntros "Hsub Hp".
    iApply Sngl_Sub_Self.
    iApply (sP_Sub' with "Hp").
    iApply Mu_Sub_Mu.
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

  Lemma sT_All_Ex_p Γ e1 p2 T1 T2 :
    Γ s⊨ e1: oAll T1 T2 -∗
    Γ s⊨p p2 : T1, 0 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ s⊨ tapp e1 (path2tm p2) : T2 .sTp[ p2 /].
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
    by rewrite sem_psubst_one_repl ?alias_paths_pv_eq_1.
  Qed.

  Lemma T_All_Ex_p Γ e1 p2 T1 T2 T2' (Hrepl : T2 .Tp[ p2 /]~ T2') :
    Γ ⊨ e1: TAll T1 T2 -∗
    Γ ⊨p p2 : T1, 0 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ ⊨ tapp e1 (path2tm p2) : T2'.
  Proof.
    iIntros "#He1 #Hp2 !> * #Hg !>".
    iDestruct (path_wp_eq with "(Hp2 Hg)") as (pw Hal%alias_paths_pv_eq_1) "_".
    iDestruct (sT_All_Ex_p with "He1 Hp2") as "{He1 Hp2} Hep".
    iApply (wp_wand with "(Hep Hg)"); iIntros "{Hep Hg} * #Hv".
    iApply (sem_psubst_one_eq Hrepl Hal with "Hv").
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
    iIntros "#HE /= !>" (ρ) "Hg"; iSpecialize ("HE" with "Hg"); iNext i.
    rewrite path_wp_pself_eq; iDestruct "HE" as (v q Hlook) "[Hpv #Htw]".
    iApply (path_wp_wand with "Hpv"). iIntros "/= !> % <-"; eauto.
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
