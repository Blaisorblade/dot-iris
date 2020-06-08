(** * Semantic lemmas on singleton types, path typing and path replacement. *)
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_language.
From D.pure_program_logic Require Import lifting.
From D Require Import iris_prelude.
From D.Dot Require Import syn path_repl rules.
From D.Dot.lr Require Import path_wp unary_lr.

Implicit Types
         (v w : vl) (t : tm) (d : dm) (ds : dms) (p q : path)
         (ρ : env) (l : label) (Pv : vl → Prop).

Set Suggest Proof Using.
Set Default Proof Using "Type".

Section semantic_lemmas.
  Context `{!dlangG Σ}.
  (** Non-pDOT rules start: *)

  Lemma sP_Sngl_Refl Γ τ p i :
    Γ s⊨p p : τ, i -∗
    Γ s⊨p p : oSing p, i.
  Proof.
    iIntros "#Hep !> %ρ Hg"; iApply (strong_path_wp_wand with "(Hep Hg)").
    iIntros "%v %Hpv _ !%"; apply alias_paths_pv_eq_1, Hpv.
  Qed.

  Lemma P_Sngl_Refl Γ T p i : Γ ⊨p p : T, i -∗ Γ ⊨p p : TSing p, i.
  Proof. apply sP_Sngl_Refl. Qed.

  Lemma sSngl_Sub_Self Γ p T i :
    Γ s⊨p p : T, i -∗
    Γ s⊨ oSing p, i <: T, i.
  Proof.
    iIntros "#Hp !> %ρ %v Hg /= Heq"; iSpecialize ("Hp" with "Hg"); iNext i.
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
    iIntros "#Hp #Hps !> %ρ %v #Hg Heq".
    iDestruct (path_wp_eq with "(Hp Hg)") as (w) "[Hpw _] {Hp}".
    rewrite -alias_paths_pv_eq_1; iSpecialize ("Hps" $! _ w with "Hg Hpw");
      iNext i; rewrite /= !alias_paths_pv_eq_1.
    iRevert "Hps Hpw Heq"; iIntros "!%" (Hqw Hpw Hqv).
    rewrite (path_wp_pure_det Hqv Hqw) {Hqv Hqw}. exact Hpw.
  Qed.

  Lemma Sngl_Sub_Sym Γ p q T i: Γ ⊨p p : T, i -∗
    Γ ⊨ TSing p, i <: TSing q, i -∗ Γ ⊨ TSing q, i <: TSing p, i.
  Proof. apply sSngl_Sub_Sym. Qed.

  Lemma sP_Sngl_Inv Γ p q i :
    Γ s⊨p p : oSing q, i -∗
    Γ s⊨p q : oTop, i.
  Proof.
    iIntros "#Hpq !> %ρ Hg /="; iSpecialize ("Hpq" with "Hg"); iNext i.
    iDestruct "Hpq" as %(v & _ & Hqv)%alias_paths_simpl%alias_paths_sameres.
    iIntros "!%". exact: (path_wp_pure_wand Hqv).
  Qed.

  Lemma P_Sngl_Inv Γ p q i : Γ ⊨p p : TSing q, i -∗ Γ ⊨p q : TTop, i.
  Proof. apply sP_Sngl_Inv. Qed.

  (** Non-pDOT rules end. *)

  (** Here we show this rule for *semantic* substitution. *)
  Lemma sSngl_pq_Sub {Γ i p q T1 T2} :
    T1 ~sTpI[ p := q ]* T2 -∗
    Γ s⊨p p : oSing q, i -∗
    Γ s⊨ T1, i <: T2, i.
  Proof.
    iIntros "#Hrepl #Hal !> %ρ %v Hg HT1".
    iSpecialize ("Hal" with "Hg"); iNext i.
    iDestruct "Hal" as %Hal%alias_paths_simpl.
    iRewrite -("Hrepl" $! vnil ρ v Hal); iExact "HT1".
  Qed.

  Lemma Sngl_pq_Sub {Γ i p q T1 T2} (Hrepl : T1 ~Tp[ p := q ]* T2):
    Γ ⊨p p : TSing q, i -∗
    Γ ⊨ T1, i <: T2, i.
  Proof.
    iApply sSngl_pq_Sub; iApply sem_ty_path_repl_eq.
    apply fundamental_ty_path_repl_rtc, Hrepl.
  Qed.

  Lemma sP_Mu_E {Γ T p i} :
    Γ s⊨p p : oMu T, i -∗ Γ s⊨p p : T .sTp[ p /], i.
  Proof.
    iIntros "#Hp !> %ρ Hg /=".
    iApply (strong_path_wp_wand with "(Hp Hg)"); iIntros "**".
    by rewrite oMu_eq sem_psubst_one_repl ?alias_paths_pv_eq_1.
  Qed.

  Lemma sP_Mu_I {Γ T p i} :
    Γ s⊨p p : T .sTp[ p /], i -∗ Γ s⊨p p : oMu T, i.
  Proof.
    iIntros "#Hp !> %ρ Hg /=".
    iApply (strong_path_wp_wand with "(Hp Hg)"); iIntros "**".
    by rewrite oMu_eq sem_psubst_one_repl ?alias_paths_pv_eq_1.
  Qed.

  (** Lifting [sP_Mu_E] and [sP_Mu_I] is a bit less easy than other lemmas,
  because we need proof of [p]'s termination to relate semantic and syntactic
  substitution on types. *)
  Lemma P_Mu_E {Γ T T' p i} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : TMu T, i -∗ Γ ⊨p p : T', i.
  Proof.
    rewrite /iptp sP_Mu_E; iIntros "#Hp !> %ρ Hg /=".
    iApply (strong_path_wp_wand with "(Hp Hg)"); iIntros "**".
    by rewrite (sem_psubst_one_eq Hrepl) ?alias_paths_pv_eq_1.
  Qed.

  Lemma P_Mu_I {Γ T T' p i} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : T', i -∗ Γ ⊨p p : TMu T, i.
  Proof.
    rewrite /iptp -sP_Mu_I; iIntros "#Hp !> %ρ Hg /=".
    iApply (strong_path_wp_wand with "(Hp Hg)"); iIntros "**".
    by rewrite (sem_psubst_one_eq Hrepl) ?alias_paths_pv_eq_1.
  Qed.

  (** But these minor difficulties don't affect proofs of [P_Mu_E] and
  [P_Mu_I] from scratch; to wit: *)
  Lemma P_Mu_E' {Γ T T' p i} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : TMu T, i -∗ Γ ⊨p p : T', i.
  Proof.
    iIntros "#Hp !> %ρ Hg /=".
    iApply (strong_path_wp_wand with "(Hp Hg)"); iIntros "**".
    by rewrite oMu_eq -(psubst_one_repl Hrepl) ?alias_paths_pv_eq_1.
  Qed.

  Lemma P_Mu_I' {Γ T T' p i} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : T', i -∗ Γ ⊨p p : TMu T, i.
  Proof.
    iIntros "#Hp !> %ρ Hg /=".
    iApply (strong_path_wp_wand with "(Hp Hg)"); iIntros "**".
    by rewrite oMu_eq -(psubst_one_repl Hrepl) ?alias_paths_pv_eq_1.
  Qed.

  Lemma sT_All_Ex_p Γ e1 p2 T1 T2 :
    Γ s⊨ e1: oAll T1 T2 -∗
    Γ s⊨p p2 : T1, 0 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ s⊨ tapp e1 (path2tm p2) : T2 .sTp[ p2 /].
  Proof.
    iIntros "#He1 #Hp2 !> %ρ #Hg !>"; iSpecialize ("Hp2" with "Hg").
    smart_wp_bind (AppLCtx _) v "Hr {He1}" ("He1" with "Hg").
    iDestruct "Hr" as (t ->) "#HvFun {Hg}"; rewrite path_wp_eq path2tm_subst.
    iDestruct "Hp2" as (pw Hpwpp) "Hpw"; iSpecialize ("HvFun" with "Hpw").
    iDestruct (path_wp_pure_to_wp Hpwpp) as "{Hpw} Hwpp".
    smart_wp_bind (AppRCtx _) w "%Heq {Hwpp}" "Hwpp"; subst w.
    rewrite -wp_pure_step_later; last done; iNext.
    iApply (wp_wand with "HvFun"). iIntros (v) "Hres".
    rewrite sem_psubst_one_repl //. apply /alias_paths_pv_eq_1 /Hpwpp.
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

  (* From pDOT *)
  Lemma sP_Fld_I Γ p T l i:
    Γ s⊨p pself p l : T, i -∗
    (*─────────────────────────*)
    Γ s⊨p p : cVMem l T, i.
  Proof.
    iIntros "#HE /= !> %ρ Hg"; iSpecialize ("HE" with "Hg"); iNext i.
    rewrite path_wp_pself_eq; iDestruct "HE" as (v q Hlook) "[Hpv #Htw]".
    iApply (path_wp_wand with "Hpv"). iIntros "/= % <-"; eauto.
  Qed.

  Lemma P_Fld_I Γ p T l i: Γ ⊨p pself p l : T, i -∗ Γ ⊨p p : TVMem l T, i.
  Proof. apply sP_Fld_I. Qed.

  (* Suppose path typing required termination *now* rather than later:

    Definition sptp `{!dlangG Σ} p i Γ (T : oltyO Σ 0): iProp Σ :=
     □∀ ρ, sG⟦Γ⟧* ρ →
-      ▷^i path_wp (p.|[ρ]) (λ v, oClose T ρ v).
+      path_wp (p.|[ρ]) (λ v, ▷^i oClose T ρ v).

  Then this lemma would already fail: the hypothesis implies that [p]
  terminates now, but that [pself p l] terminates *only under later^i*!
  *)
  Lemma sP_Fld_E {Γ} p T l i:
    Γ s⊨p p : cVMem l T, i -∗
    (*─────────────────────────*)
    Γ s⊨p pself p l : T, i.
  Proof.
    iIntros "#HE !> %ρ HG /="; iSpecialize ("HE" with "HG"); iNext i.
    rewrite path_wp_pself_eq path_wp_eq.
    iDestruct "HE" as (vp Hpv d Hlook pmem ->) "#H".
    iExists vp, pmem. eauto.
  Qed.
  (* In the above proof, in contrast with [sT_Obj_E], lots of the lemmas
     needed of path_wp hold simply by computation. *)

  Lemma P_Fld_E {Γ} p T l i:
    Γ ⊨p p : TVMem l T, i -∗
    (*─────────────────────────*)
    Γ ⊨p pself p l : T, i.
  Proof. apply sP_Fld_E. Qed.

  Lemma sP_Sngl_Trans Γ p q T i:
    Γ s⊨p p : oSing q, i -∗
    Γ s⊨p q : T, i -∗
    Γ s⊨p p : T, i.
  Proof.
    iIntros "#Hep #Heq !> %ρ #Hg"; iSpecialize ("Heq" with "Hg").
    iSpecialize ("Hep" with "Hg"); iNext i.
    by iDestruct "Hep" as %->%alias_paths_simpl%(alias_paths_elim_eq (T _ _)).
  Qed.

  Lemma P_Sngl_Trans Γ p q T i:
    Γ ⊨p p : TSing q, i -∗ Γ ⊨p q : T, i -∗ Γ ⊨p p : T, i.
  Proof. apply sP_Sngl_Trans. Qed.

  Lemma sP_Sngl_E Γ τ p q l i:
    Γ s⊨p p : oSing q, i -∗
    Γ s⊨p pself q l : τ, i -∗
    Γ s⊨p pself p l : oSing (pself q l), i.
  Proof.
    iIntros "#Hpq #HqlT !> %ρ #Hg"; iSpecialize ("HqlT" with "Hg");
    iSpecialize ("Hpq" with "Hg"); iNext i; iClear "Hg".
    iDestruct "Hpq" as %Hal%alias_paths_simpl.
    rewrite !path_wp_eq; iDestruct "HqlT" as (vql Hql) "_".
    iIntros "!% /="; setoid_rewrite alias_paths_pv_eq_1.
    apply /alias_paths_sameres /alias_paths_pself /Hal /Hql.
  Qed.

  Lemma P_Sngl_E Γ T p q l i: Γ ⊨p p : TSing q, i -∗ Γ ⊨p pself q l : T, i -∗
    Γ ⊨p pself p l : TSing (pself q l), i.
  Proof. apply sP_Sngl_E. Qed.

  Lemma sP_ISub {Γ p T1 T2 i j}:
    Γ s⊨p p : T1, i -∗
    Γ s⊨ T1, i <: T2, i + j -∗
    (*───────────────────────────────*)
    Γ s⊨p p : T2, i + j.
  Proof.
    iIntros "/= * #HpT1 #Hsub !> * #Hg".
    iSpecialize ("HpT1" with "Hg").
    rewrite !path_wp_eq.
    iDestruct "HpT1" as (v) "Hpv"; iExists v.
    iDestruct "Hpv" as "[$ HpT1] {Hpv}". by iApply "Hsub".
  Qed.

End semantic_lemmas.
