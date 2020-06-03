(** * Unstamped semantic judgments, adequacy, and typing lemmas. *)
From D Require Export iris_prelude swap_later_impl.
From D.pure_program_logic Require Import weakestpre.
From D Require Import iris_extra.det_reduction.
From D.Dot Require Import skeleton path_repl typing_aux_defs.
From D.Dot Require Import unary_lr.
From D.Dot Require Import later_sub_sem binding_lr path_repl_lr defs_lr dsub_lr prims_lr.
From stdpp Require Import relations.
(* Fix scope. *)
Import dlang_adequacy D.prelude stdpp.relations stdpp.tactics.

Implicit Types (Σ : gFunctors)
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : env) (l : label).

(* XXX *)
Arguments bupd {_}%type_scope {_} _%bi_scope.
Notation "|==> Q" := (bupd Q) : bi_scope.

Section unstamped_judgs.
  Context `{!dlangG Σ}.

  (* Semantic, Unstamped, Expression TyPing *)
  Definition suetp e_u Γ T : iProp Σ :=
    □ |==> ∃ e_s, ⌜ same_skel_tm e_u e_s⌝ ∧ Γ s⊨ e_s : T.

  Definition sudstp ds_u Γ T : iProp Σ :=
    □ |==> ∃ ds_s, ⌜ same_skel_dms ds_u ds_s⌝ ∧ Γ s⊨ds ds_s : T.

  Definition sudtp l d_u Γ T : iProp Σ :=
    □ |==> ∃ d_s, ⌜ same_skel_dm d_u d_s⌝ ∧ Γ s⊨ { l := d_s } : T.

  Definition iudtp  Γ T l d     := sudtp l d  V⟦Γ⟧* C⟦T⟧.
  Definition iudstp Γ T ds      := sudstp ds  V⟦Γ⟧* C⟦T⟧.
  Definition iuetp  Γ T e       := suetp e    V⟦Γ⟧* V⟦T⟧.
End unstamped_judgs.

Global Instance: Params (@suetp) 3 := {}.
Global Instance: Params (@sudstp) 3 := {}.
Global Instance: Params (@sudtp) 4 := {}.

Section unstamped_judgs_proper.
  Context `{!dlangG Σ}.

  Global Instance suetp_proper e : Proper ((≡) ==> (≡) ==> (≡)) (suetp e).
  Proof. rewrite /suetp => ??????. by repeat f_equiv. Qed.
  Global Instance suetp_flip_proper e :
    Proper (flip (≡) ==> flip (≡) ==> flip (≡)) (suetp e).
  Proof. apply: flip_proper_3. Qed.

  Global Instance sudstp_proper ds : Proper ((≡) ==> (≡) ==> (≡)) (sudstp ds).
  Proof. rewrite /sudstp => ??????; by repeat f_equiv. Qed.
  Global Instance sudstp_flip_proper ds :
    Proper (flip (≡) ==> flip (≡) ==> flip (≡)) (sudstp ds).
  Proof. apply: flip_proper_3. Qed.

  Global Instance sudtp_proper l d : Proper ((≡) ==> (≡) ==> (≡)) (sudtp l d).
  Proof. rewrite /sudtp => ??????. by repeat f_equiv. Qed.
  Global Instance sudtp_flip_proper l d :
    Proper (flip (≡) ==> flip (≡) ==> flip (≡)) (sudtp l d).
  Proof. apply: flip_proper_3. Qed.
End unstamped_judgs_proper.

Notation "Γ su⊨ e : T" := (suetp e Γ T) (at level 74, e, T at next level).
Notation "Γ su⊨ {  l := d  } : T" := (sudtp l d Γ T) (at level 64, d, l, T at next level).
Notation "Γ su⊨ds ds : T" := (sudstp ds Γ T) (at level 74, ds, T at next level).

Notation "Γ u⊨ {  l := d  } : T" := (iudtp Γ T l d) (at level 74, d, l, T at next level).
Notation "Γ u⊨ds ds : T" := (iudstp Γ T ds) (at level 74, ds, T at next level).
Notation "Γ u⊨ e : T" := (iuetp Γ T e) (at level 74, e, T at next level).

(* Adequacy *)
Theorem unstamped_s_safety_dot_sem Σ `{HdlangG: !dlangPreG Σ} `{!SwapPropI Σ}
  {e_u}
  (τ : ∀ `{!dlangG Σ}, olty Σ 0)
  (Hwp : ∀ `{!dlangG Σ} `(!SwapPropI Σ), ⊢ [] su⊨ e_u : τ):
  safe e_u.
Proof.
  intros e_u' [n Hsteps]%rtc_nsteps.
  eapply same_skel_safe_n_impl, Hsteps.
  apply (soundness (M := iResUR Σ) _ n).
  apply (bupd_plain_soundness _).
  (* XXX [hG] is needed, till I fix everything and drop the second map. *)
  iMod (gen_iheap_init (L := stamp) ∅) as (hG) "_".
  set (DLangΣ := DLangG Σ).
  iDestruct (Hwp DLangΣ SwapPropI0) as "#>Hwp".
  iDestruct "Hwp" as (e_s Hsim) "#Hwp /=".
  iSpecialize ("Hwp" $! ids with "[//]").
  rewrite hsubst_id (wptp_safe_n n).
  iIntros "!>!>"; iDestruct ("Hwp") as %Hsafe; naive_solver.
Qed.

Corollary unstamped_safety_dot_sem Σ `{HdlangG: !dlangPreG Σ} `{!SwapPropI Σ}
  {e T}
  (Hlog : ∀ `(!dlangG Σ) `(!SwapPropI Σ), ⊢ [] u⊨ e : T):
  safe e.
Proof. exact: (unstamped_s_safety_dot_sem Σ (λ _, V⟦T⟧)). Qed.

Lemma same_skel_dms_hasnt ds ds' l : dms_hasnt ds l → same_skel_dms ds ds' → dms_hasnt ds' l.
Proof.
  rewrite /dms_hasnt; elim: ds ds' => [| [s d] ds IH] [|[s' d'] ds'] //= ? [<-{s'} ?].
  case_match; naive_solver.
Qed.
Hint Resolve same_skel_dms_hasnt : core.

Section unstamped_lemmas.
  Context `{!dlangG Σ}.

  Lemma suT_All_E {Γ e1 e2 T1 T2}:
    Γ su⊨ e1 : oAll T1 (shift T2) -∗
    Γ su⊨ e2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ su⊨ tapp e1 e2 : T2.
  Proof.
    iIntros "#H1 #H2 !>".
    iMod "H1" as (e1s Hsk1) "H1"; iMod "H2" as (e2s Hsk2) "H2"; iModIntro.
    by iExists (tapp e1s e2s); iSplit; last iApply (sT_All_E with "H1 H2").
  Qed.

  Lemma uT_All_E {Γ e1 e2 T1 T2} :
    Γ u⊨ e1 : TAll T1 (shift T2) -∗ Γ u⊨ e2 : T1 -∗ Γ u⊨ tapp e1 e2 : T2.
  Proof.
    iIntros "#H1 #H2 !>".
    iMod "H1" as (e1s Hsk1) "H1"; iMod "H2" as (e2s Hsk2) "H2"; iModIntro.
    by iExists (tapp e1s e2s); iSplit; last iApply (T_All_E with "H1 H2").
  Qed.

  Lemma suT_All_Ex_p {Γ e1 p2 T1 T2} :
    Γ su⊨ e1 : oAll T1 T2 -∗
    Γ s⊨p p2 : T1, 0 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ su⊨ tapp e1 (path2tm p2) : T2 .sTp[ p2 /].
  Proof.
    iIntros "#H1 #H2 !>"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    by iExists (tapp e1s (path2tm p2)); iSplit; last iApply (sT_All_Ex_p with "H1 H2").
  Qed.

  Lemma uT_All_Ex_p Γ e1 p2 T1 T2 T2' (Hrepl : T2 .Tp[ p2 /]~ T2') :
    Γ u⊨ e1: TAll T1 T2 -∗
    Γ ⊨p p2 : T1, 0 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ u⊨ tapp e1 (path2tm p2) : T2'.
  Proof.
    iIntros "#H1 #H2 !>"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    by iExists (tapp e1s (path2tm p2)); iSplit; last iApply (T_All_Ex_p with "H1 H2").
  Qed.

  Lemma suT_All_Ex {Γ e1 v2 T1 T2} :
    Γ su⊨ e1 : oAll T1 T2 -∗
    Γ s⊨p pv v2 : T1, 0 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ su⊨ tapp e1 (tv v2) : T2.|[ v2 /].
  Proof.
    iIntros "#H1 #H2 !>"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    iExists (tapp e1s (tv v2)); iSplit; last iApply (sT_All_Ex with "H1").
    done.
    by iApply (sT_Path (p := pv v2)).
  Qed.

  Lemma suT_Obj_E {Γ e T l}:
    Γ su⊨ e : cVMem l T -∗
    Γ su⊨ tproj e l : T.
  Proof.
    iIntros "#H1 !>"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    by iExists (tproj e1s l); iSplit; last iApply (sT_Obj_E with "H1").
  Qed.

  Lemma suT_All_I_Strong {Γ Γ'} T1 T2 e
    (Hctx : s⊨G Γ <:* oLater <$> Γ') :
    shift T1 :: Γ' su⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ su⊨ tv (vabs e) : oAll T1 T2.
  Proof.
    iIntros "#H1 !>"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    by iExists (tv (vabs e1s)); iSplit; last iApply (sT_All_I_Strong with "H1").
  Qed.

  Lemma uT_All_I_Strong {Γ Γ'} T1 T2 e
    (Hctx : ⊨G Γ <:* TLater <$> Γ') :
    shift T1 :: Γ' u⊨ e : T2 -∗
    Γ u⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "#H1 !>"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    by iExists (tv (vabs e1s)); iSplit; last iApply (T_All_I_Strong with "H1").
  Qed.

  Lemma suT_All_I {Γ} T1 T2 e:
    shift T1 :: Γ su⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ su⊨ tv (vabs e) : oAll T1 T2.
  Proof.
    apply suT_All_I_Strong => ρ. rewrite senv_TLater_commute. by iIntros "$".
  Qed.

  Lemma suT_Skip Γ e T :
    Γ su⊨ e : oLater T -∗
    Γ su⊨ tskip e : T.
  Proof.
    iIntros "#H1 !>"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    by iExists (tskip e1s); iSplit; last iApply (sT_Skip with "H1").
  Qed.

  Lemma suT_DSub {Γ e T1 T2}:
    Γ su⊨ e : T1 -∗
    Γ s⊨ T1 <:[0] T2 -∗
    Γ su⊨ e : T2.
  Proof.
    iIntros "#H1 #H2 !>"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    by iExists e1s; iSplit; last iApply (sT_DSub with "H1 H2").
  Qed.


  Lemma suT_Obj_I (Γ : sCtx Σ) (T : clty Σ) ds:
    oLater T :: Γ su⊨ds ds : T -∗
    Γ su⊨ tv (vobj ds) : oMu T.
  Proof.
    iIntros "#H1 !>"; iMod "H1" as (ds1 Hsk1) "H1"; iModIntro.
    by iExists (tv (vobj ds1)); iSplit; last iApply (sT_Obj_I with "H1").
  Qed.

  Lemma uT_Obj_I Γ T ds:
    TLater T :: Γ u⊨ds ds : T -∗
    Γ u⊨ tv (vobj ds) : TMu T.
  Proof. apply suT_Obj_I. Qed.

  Lemma suT_Path Γ τ p :
    Γ s⊨p p : τ, 0 -∗ Γ su⊨ path2tm p : τ.
  Proof.
    iIntros "#H1 !>"; iModIntro.
    by iExists (path2tm p); iSplit; last iApply (sT_Path with "H1").
  Qed.
  (* Primitives *)

  Lemma suT_Un Γ u e1 B1 Br (Hu : un_op_semtype u B1 Br) :
    Γ su⊨ e1 : oPrim B1 -∗
    Γ su⊨ tun u e1 : oPrim Br.
  Proof.
    iIntros "#H1 !>"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    by iExists (tun u e1s); iSplit; last iApply (sT_Un with "H1").
  Qed.

  Lemma uT_Un Γ u e1 B1 Br (Hu : un_op_syntype u B1 Br) :
    Γ u⊨ e1 : TPrim B1 -∗
    Γ u⊨ tun u e1 : TPrim Br.
  Proof.
    iIntros "#H1 !>"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    by iExists (tun u e1s); iSplit; last iApply (T_Un with "H1").
  Qed.

  Lemma suT_Bin Γ b e1 e2 B1 B2 Br (Hu : bin_op_semtype b B1 B2 Br (const (const True))) :
    Γ su⊨ e1 : oPrim B1 -∗
    Γ su⊨ e2 : oPrim B2 -∗
    Γ su⊨ tbin b e1 e2 : oPrim Br.
  Proof.
    iIntros "#H1 #H2 !>".
    iMod "H1" as (e1s Hsk1) "H1"; iMod "H2" as (e2s Hsk2) "H2"; iModIntro.
    by iExists (tbin b e1s e2s); iSplit; last iApply (sT_Bin with "H1 H2").
  Qed.

  Lemma uT_Bin Γ b e1 e2 B1 B2 Br (Hu : bin_op_syntype b B1 B2 Br) :
    Γ u⊨ e1 : TPrim B1 -∗
    Γ u⊨ e2 : TPrim B2 -∗
    Γ u⊨ tbin b e1 e2 : TPrim Br.
  Proof.
    iIntros "#H1 #H2 !>".
    iMod "H1" as (e1s Hsk1) "H1"; iMod "H2" as (e2s Hsk2) "H2"; iModIntro.
    by iExists (tbin b e1s e2s); iSplit; last iApply (T_Bin with "H1 H2").
  Qed.

  Lemma suT_If Γ e1 e2 e3 T :
    Γ su⊨ e1 : oBool -∗ Γ su⊨ e2 : T -∗ Γ su⊨ e3 : T -∗
    Γ su⊨ tif e1 e2 e3 : T.
  Proof.
    iIntros "#H1 #H2 #H3 !>".
    iMod "H1" as (e1s Hsk1) "H1"; iMod "H2" as (e2s Hsk2) "H2";
    iMod "H3" as (e3s Hsk3) "H3"; iModIntro.
    by iExists (tif e1s e2s e3s); iSplit; last iApply (sT_If with "H1 H2 H3").
  Qed.

  Lemma suD_Nil Γ : ⊢ Γ su⊨ds [] : cTop.
  Proof. iExists []. by rewrite -sD_Nil. Qed.

  Lemma suD_Cons Γ d1 ds2 l (T1 T2 : cltyO Σ)
    (Hlds : dms_hasnt ds2 l) :
    Γ su⊨ { l := d1 } : T1 -∗ Γ su⊨ds ds2 : T2 -∗
    Γ su⊨ds (l, d1) :: ds2 : cAnd T1 T2.
  Proof.
    iIntros "#H1 #H2 !>".
    iMod "H1" as (d1s Hsk1) "H1"; iMod "H2" as (ds2s Hsk2) "H2"; iModIntro.
    iExists ((l, d1s) :: ds2s); iSplit; last iApply (sD_Cons with "H1 H2");
      naive_solver.
  Qed.

  Lemma suD_Val {Γ} T v1 l:
    Γ su⊨ tv v1 : T -∗
    Γ su⊨ { l := dpt (pv v1) } : cVMem l T.
  Proof.
    iIntros "#H1 !>"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    destruct (same_skel_tv_tv Hsk1) as [v1s ->].
    by iExists (dpt (pv v1s)); iSplit; last iApply (sD_Val with "H1").
  Qed.

  Lemma suD_Path {Γ} T p l:
    Γ s⊨p p : T, 0 -∗
    Γ su⊨ { l := dpt p } : cVMem l T.
  Proof.
    iIntros "#H1 !>"; iModIntro.
    by iExists (dpt p); iSplit; last iApply (sD_Path with "H1").
  Qed.

  Lemma suD_Val_New {Γ l ds} {T : clty Σ}:
    oAnd (oLater T) (oSing (pself (pv (ids 1)) l)) :: Γ su⊨ds ds : T -∗
    Γ su⊨ { l := dpt (pv (vobj ds)) } : cVMem l (oMu (clty_olty T)).
  Proof.
    iIntros "#H1 !>"; iMod "H1" as (ds1s Hsk1) "H1"; iModIntro.
    by iExists (dpt (pv (vobj ds1s))); iSplit; last iApply (sD_Val_New with "H1").
  Qed.

  Lemma suD_Path_Stp {Γ T1 T2 p1 l}:
    Γ s⊨ T1 <:[0] T2 -∗
    Γ su⊨ { l := dpt p1 } : cVMem l T1 -∗
    Γ su⊨ { l := dpt p1 } : cVMem l T2.
  Proof.
    iIntros "#Hsub #H1 !>"; iMod "H1" as (d1s Hsk1) "H1"; iModIntro.
    destruct (same_skel_dpt_dpt Hsk1) as [p1s ->].
    by iExists (dpt p1s); iSplit; last iApply (sD_Path_Stp with "Hsub H1").
  Qed.
End unstamped_lemmas.

(* For storeless typing. *)
Section storeless_unstamped_lemmas.
  Context `{!dlangG Σ}.

  (* Lemma suT_Var {Γ x τ}
    (Hx : Γ !! x = Some τ):
    (*──────────────────────*)
    ⊢ Γ su⊨ of_val (ids x) : shiftN x τ.
  Proof. repeat iModIntro; by iExists (of_val (ids x)); iSplit; last iApply sT_Var. Qed.
  *)

  (* Lemma uT_Var {Γ x τ}
    (Hx : Γ !! x = Some τ):
    (*──────────────────────*)
    ⊢ Γ u⊨ of_val (ids x) : shiftN x τ.
  Proof.
    repeat iModIntro; by iExists (tv (ids x)); iSplit; last iApply T_Var.
  Qed. *)

  Lemma uT_Sub {Γ e T1 T2 i}:
    Γ u⊨ e : T1 -∗ Γ ⊨ T1, 0 <: T2, i -∗ Γ u⊨ iterate tskip i e : T2.
  Proof.
    iIntros "#H1 #Hsub !>"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    iExists (iterate tskip i e1s); iSplit; last iApply (T_Sub with "H1 Hsub").
    eauto using same_skel_tm_tskips.
  Qed.

  Lemma suetp_var Γ x T :
    Γ su⊨ tv (ids x) : T ==∗ Γ s⊨ tv (ids x) : T.
  Proof.
    iIntros "#H1"; iMod "H1" as (e1s Hsk1) "H1".
    by rewrite (same_skel_tv_var_tv_var Hsk1).
  Qed.

  Lemma suetp_vlit Γ b T :
    Γ su⊨ tv (vlit b) : T ==∗ Γ s⊨ tv (vlit b) : T.
  Proof.
    iIntros "#H1"; iMod "H1" as (e1s Hsk1) "H1".
    by rewrite (same_skel_tv_vlit_tv_vlit Hsk1).
  Qed.

  Lemma uT_All_Ex {Γ e1 x2 T1 T2}:
    Γ u⊨ e1: TAll T1 T2 -∗ Γ u⊨ tv (ids x2) : T1 -∗ Γ u⊨ tapp e1 (tv (ids x2)) : T2.|[ids x2/].
  Proof.
    iIntros "#H1 #H2 !>"; iMod "H1" as (e1s Hsk1) "H1".
    iMod (suetp_var with "H2") as "{H2} H2"; iModIntro.
    by iExists (tapp e1s (tv (ids x2))); iSplit; last iApply (T_All_Ex with "H1 H2").
  Qed.

  Lemma suetp_var_lift1 {Γ} x T1 T2:
    □(Γ s⊨ tv (ids x) : T1 -∗ Γ s⊨ tv (ids x) : T2) ⊢
    Γ su⊨ tv (ids x) : T1 -∗ Γ su⊨ tv (ids x) : T2.
  Proof.
    iIntros "#Hr #H1 !>"; iMod (suetp_var with "H1") as "{H1} H1"; iModIntro.
    by iExists (tv (ids x)); iSplit; last iApply ("Hr" with "H1").
  Qed.

  (* Lemma uT_Mu_I {Γ} T x: Γ u⊨ tv (ids x) : T.|[ids x/] -∗ Γ u⊨ tv (ids x) : TMu T.
  Proof. iApply suetp_var_lift1; iModIntro; iApply T_Mu_I. Qed.

  Lemma uT_Mu_E {Γ} T x: Γ u⊨ tv (ids x) : TMu T -∗ Γ u⊨ tv (ids x) : T.|[ids x/].
  Proof. iApply suetp_var_lift1; iModIntro; iApply T_Mu_E. Qed. *)

  (* These ones don't work, see the update modality. Change the typing judgment! *)
  (* Lemma bad_uP_Var {Γ} x T:
    Γ u⊨ tv (var_vl x) : T ==∗
    Γ ⊨p pv (var_vl x) : T, 0.
  Proof.
    iIntros "H1"; iMod (suetp_var with "H1") as "H1"; iModIntro.
    by iApply sP_Val.
  Qed.

  Lemma bad_uP_Lit {Γ} b T:
    Γ u⊨ tv (vlit b) : T ==∗
    Γ ⊨p pv (vlit b) : T, 0.
  Proof.
    iIntros "H1"; iMod (suetp_vlit with "H1") as "H1"; iModIntro.
    by iApply sP_Val.
  Qed. *)

End storeless_unstamped_lemmas.
