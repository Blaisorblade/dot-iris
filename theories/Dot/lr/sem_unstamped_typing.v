(** * Unstamped semantic judgments, adequacy, and typing lemmas. *)
From D Require Export iris_prelude swap_later_impl.
From D.pure_program_logic Require Import weakestpre adequacy.
From D Require Import iris_extra.det_reduction.
From D.Dot Require Import skeleton path_repl typing_aux_defs.
From D.Dot Require Import unary_lr.
From D.Dot Require Import later_sub_sem binding_lr path_repl_lr defs_lr dsub_lr prims_lr.
From stdpp Require Import relations.
(* Fix what is in scope. *)
Import stdpp.relations stdpp.tactics D.prelude dlang_adequacy.

Implicit Types (Σ : gFunctors)
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : env) (l : label).

Section unstamped_judgs.
  Context `{!dlangG Σ}.

  (* Semantic, Unstamped, Expression TyPing *)
  Definition suetp e_u Γ T : iProp Σ :=
    |==> ∃ e_s, ⌜ same_skel_tm e_u e_s⌝ ∧ Γ s⊨ e_s : T.

  Definition sudstp ds_u Γ T : iProp Σ :=
    |==> ∃ ds_s, ⌜ same_skel_dms ds_u ds_s⌝ ∧ Γ s⊨ds ds_s : T.

  Definition sudtp l d_u Γ T : iProp Σ :=
    |==> ∃ d_s, ⌜ same_skel_dm d_u d_s⌝ ∧ Γ s⊨ { l := d_s } : T.

  Definition iuetp  Γ T e       := suetp e    V⟦Γ⟧* V⟦T⟧.
  Definition iudstp Γ T ds      := sudstp ds  V⟦Γ⟧* C⟦T⟧.
  Definition iudtp  Γ T l d     := sudtp l d  V⟦Γ⟧* C⟦T⟧.

  Arguments suetp  : simpl never.
  Arguments sudstp : simpl never.
  Arguments sudtp  : simpl never.
  Arguments iuetp  : simpl never.
  Arguments iudstp : simpl never.
  Arguments iudtp  : simpl never.
End unstamped_judgs.

#[global] Instance: Params (@suetp) 3 := {}.
#[global] Instance: Params (@sudstp) 3 := {}.
#[global] Instance: Params (@sudtp) 4 := {}.

Section unstamped_judgs_proper.
  Context `{!dlangG Σ}.

  #[global] Instance suetp_proper e : Proper ((≡) ==> (≡) ==> (≡)) (suetp e).
  Proof. rewrite /suetp => ??????. by repeat f_equiv. Qed.
  #[global] Instance suetp_flip_proper e :
    Proper (flip (≡) ==> flip (≡) ==> flip (≡)) (suetp e).
  Proof. apply: flip_proper_3. Qed.

  #[global] Instance sudstp_proper ds : Proper ((≡) ==> (≡) ==> (≡)) (sudstp ds).
  Proof. rewrite /sudstp => ??????; by repeat f_equiv. Qed.
  #[global] Instance sudstp_flip_proper ds :
    Proper (flip (≡) ==> flip (≡) ==> flip (≡)) (sudstp ds).
  Proof. apply: flip_proper_3. Qed.

  #[global] Instance sudtp_proper l d : Proper ((≡) ==> (≡) ==> (≡)) (sudtp l d).
  Proof. rewrite /sudtp => ??????. by repeat f_equiv. Qed.
  #[global] Instance sudtp_flip_proper l d :
    Proper (flip (≡) ==> flip (≡) ==> flip (≡)) (sudtp l d).
  Proof. apply: flip_proper_3. Qed.
End unstamped_judgs_proper.

Notation "Γ su⊨ e : T" := (suetp e Γ T) (at level 74, e, T at next level).
Notation "Γ su⊨ {  l := d  } : T" := (sudtp l d Γ T) (at level 64, d, l, T at next level).
Notation "Γ su⊨ds ds : T" := (sudstp ds Γ T) (at level 74, ds, T at next level).

Notation "Γ u⊨ {  l := d  } : T" := (iudtp Γ T l d) (at level 74, d, l, T at next level).
Notation "Γ u⊨ds ds : T" := (iudstp Γ T ds) (at level 74, ds, T at next level).
Notation "Γ u⊨ e : T" := (iuetp Γ T e) (at level 74, e, T at next level).

Theorem unstamped_s_safety_dot_sem
  Σ `{HdlangG : !dlangG Σ} `{HswapProp : !SwapPropI Σ}
  {e_u}
  (τ : ∀ `{!dlangG Σ}, olty Σ 0)
  (Hwp : ∀ `{!dlangG Σ} `(!SwapPropI Σ), ⊢ [] su⊨ e_u : τ):
  safe e_u.
Proof.
  intros e_u' [n Hsteps]%rtc_nsteps.
  apply (soundness (M := iResUR Σ) _ n).
  apply (bupd_plain_soundness _).
  iDestruct (Hwp HdlangG HswapProp) as "#>Hwp".
  iDestruct "Hwp" as (e_s Hsim) ">#Hwp".
  iSpecialize ("Hwp" $! ids with "[//]").
  rewrite hsubst_id /= (wptp_safe_n n).
  iIntros "!>!>"; iDestruct "Hwp" as %Hsafe; iIntros "!%".
  eapply same_skel_safe_n_impl, Hsteps; naive_solver.
Qed.

(** ** Adequacy of unstamped semantic typing (Theorem 5.4).
semantically well-typed terms are safe. *)
Corollary unstamped_safety_dot_sem Σ `{HdlangG: !dlangG Σ} `{!SwapPropI Σ}
  {e T}
  (Hlog : ∀ `(!dlangG Σ) `(!SwapPropI Σ), ⊢ [] u⊨ e : T):
  safe e.
Proof. exact: (unstamped_s_safety_dot_sem Σ (λ _, V⟦T⟧)). Qed.

Lemma same_skel_dms_hasnt ds ds' l : dms_hasnt ds l → same_skel_dms ds ds' → dms_hasnt ds' l.
Proof.
  rewrite /dms_hasnt; elim: ds ds' => [| [s d] ds IH] [|[s' d'] ds'] //= ? [<-{s'} ?].
  case_match; naive_solver.
Qed.

#[local] Hint Resolve same_skel_dms_hasnt : core.

Definition coveringσ `{!dlangG Σ} {i} σ (T : olty Σ i) : Prop :=
  ∀ args ρ, T args ρ ≡ T args (∞ σ.|[ρ]).

Section coveringσ_intro_lemmas.
  Context `{!dlangG Σ}.

  Lemma nclosed_syn_coveringσ {n} {T : ty} (Hcl : nclosed T n) :
    coveringσ (idsσ n) V⟦T⟧.
  Proof.
    move=> args ρ v /=.
    by rewrite -interp_finsubst_commute_cl ?length_idsσ // closed_subst_idsρ.
  Qed.

  (* Maybe hard to use in general; [nclosed] requires equality on the nose? *)
  Lemma nclosed_sem_coveringσ {n} {T : olty Σ 0} (Hcl : nclosed T n) :
    coveringσ (idsσ n) T.
  Proof.
    move=> args ρ v.
    by rewrite -olty_finsubst_commute_cl ?length_idsσ // closed_subst_idsρ.
  Qed.

  Lemma coveringσ_shift {i} σ (T : olty Σ i) :
    coveringσ σ T → coveringσ (push_var σ) (shift T).
  Proof.
    move => + args ρ => /(_ args (stail ρ)) HclT; cbn.
    rewrite /= !olty_weaken_one hsubst_comp stail_eq.
    apply HclT.
  Qed.
End coveringσ_intro_lemmas.

Section tmem_unstamped_lemmas.
  Context `{!dlangG Σ}.

  Lemma leadsto_envD_equiv_alloc {σ i} {T : olty Σ i}
    (Hcl : coveringσ σ T): ⊢ |==> ∃ s, s ↝[ σ ] T.
  Proof.
    iMod (saved_ho_sem_type_alloc _ T) as (s) "#Hs"; iIntros "!>".
    iExists s, T; iFrame "Hs"; iIntros "!%". apply Hcl.
  Qed.

  Lemma leadsto_envD_equiv_alloc_shift {σ} {T : olty Σ 0} :
    coveringσ σ T →
    ⊢ |==> ∃ s, s ↝[ push_var σ ] shift T.
  Proof. intros Hcl; apply leadsto_envD_equiv_alloc, coveringσ_shift, Hcl. Qed.

  Lemma suD_Typ_Gen {l Γ fakeT s σ} {T : olty Σ 0} :
    s ↝[ σ ] T -∗ Γ su⊨ { l := dtysyn fakeT } : cTMem l (oLater T) (oLater T).
  Proof.
    iIntros "#Hs"; iModIntro. iExists (dtysem σ s).
    iSplit; first done; iApply (sD_Typ with "Hs").
  Qed.

  Lemma suD_Typ {l σ Γ fakeT} {T : olty Σ 0} (HclT : coveringσ σ T):
    ⊢ Γ su⊨ { l := dtysyn fakeT } : cTMem l (oLater T) (oLater T).
  Proof.
    iMod (leadsto_envD_equiv_alloc HclT) as (s) "#Hs".
    iApply (suD_Typ_Gen with "Hs").
  Qed.


  (** Unstamped typing only asserts that the subject _bisimulates_ a
  semantically typed stamped value, so type definitions in the subject are
  ignored. *)
  Lemma sudtp_respects_skel_sym {Γ l d1 d2 T}
    (Hsk : same_skel_dm d1 d2) :
    Γ su⊨ { l := d1 } : T -∗
    Γ su⊨ { l := d2 } : T.
  Proof.
    iIntros "#H1"; iMod "H1" as (d1s Hsk1) "H1"; iModIntro.
    iExists d1s; iSplit; last done; iIntros "!%".
    apply /same_skel_trans_dm /Hsk1 /same_skel_symm_dm /Hsk.
  Qed.

  Lemma suD_Typ_Stp {Γ} L1 L2 U1 U2 d l:
    Γ s⊨ L2 <:[0] L1 -∗
    Γ s⊨ U1 <:[0] U2 -∗
    Γ su⊨ { l := d } : cTMem l L1 U1 -∗
    Γ su⊨ { l := d } : cTMem l L2 U2.
  Proof.
    iIntros "#Hsub1 #Hsub2 #H1"; iMod "H1" as (d1s Hsk1) "#H1"; iModIntro.
    by iExists d1s; iSplit; last iApply (sD_Typ_Stp with "Hsub1 Hsub2 H1").
  Qed.

  Lemma suD_Typ_Abs {l σ Γ L T U} fakeT (HclT : coveringσ σ T):
    Γ s⊨ L <:[0] oLater T -∗
    Γ s⊨ oLater T <:[0] U -∗
    Γ su⊨ { l := dtysyn fakeT } : cTMem l L U.
  Proof.
    by iIntros "H1 H2"; iApply (suD_Typ_Stp with "H1 H2"); iApply suD_Typ.
  Qed.

  Lemma uD_Typ_Abs {l n Γ L T U} fakeT (HclT : nclosed T n):
    Γ ⊨ L <:[0] TLater T -∗
    Γ ⊨ TLater T <:[0] U -∗
    Γ u⊨ { l := dtysyn fakeT } : TTMem l L U.
  Proof. have := !!nclosed_syn_coveringσ HclT; apply suD_Typ_Abs. Qed.

  Lemma uD_Typ {l n Γ T} fakeT (HclT : nclosed T n):
    ⊢ Γ u⊨ { l := dtysyn fakeT } : TTMem l (TLater T) (TLater T).
  Proof. have := !!nclosed_syn_coveringσ HclT; apply suD_Typ. Qed.
End tmem_unstamped_lemmas.

Section unstamped_lemmas.
  Context `{!dlangG Σ}.

  Lemma suT_All_E {Γ e1 e2 T1 T2}:
    Γ su⊨ e1 : oAll T1 (shift T2) -∗
    Γ su⊨ e2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ su⊨ tapp e1 e2 : T2.
  Proof.
    iIntros "#H1 #H2".
    iMod "H1" as (e1s Hsk1) "H1"; iMod "H2" as (e2s Hsk2) "H2"; iModIntro.
    by iExists (tapp e1s e2s); iSplit; last iApply (sT_All_E with "H1 H2").
  Qed.

  Lemma uT_All_E {Γ e1 e2 T1 T2} :
    Γ u⊨ e1 : TAll T1 (shift T2) -∗ Γ u⊨ e2 : T1 -∗ Γ u⊨ tapp e1 e2 : T2.
  Proof.
    iIntros "#H1 #H2".
    iMod "H1" as (e1s Hsk1) "H1"; iMod "H2" as (e2s Hsk2) "H2"; iModIntro.
    by iExists (tapp e1s e2s); iSplit; last iApply (T_All_E with "H1 H2").
  Qed.

  Lemma suT_All_E_p {Γ e1 p2 T1 T2} :
    Γ su⊨ e1 : oAll T1 T2 -∗
    Γ s⊨p p2 : T1, 0 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ su⊨ tapp e1 (path2tm p2) : T2 .sTp[ p2 /].
  Proof.
    iIntros "#H1 #H2"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    by iExists (tapp e1s (path2tm p2)); iSplit; last iApply (sT_All_E_p with "H1 H2").
  Qed.

  Lemma uT_All_E_p Γ e1 p2 T1 T2 T2' (Hrepl : T2 .Tp[ p2 /]~ T2') :
    Γ u⊨ e1: TAll T1 T2 -∗
    Γ ⊨p p2 : T1, 0 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ u⊨ tapp e1 (path2tm p2) : T2'.
  Proof.
    iIntros "#H1 #H2"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    by iExists (tapp e1s (path2tm p2)); iSplit; last iApply (T_All_E_p with "H1 H2").
  Qed.

  Lemma suT_All_Ex {Γ e1 v2 T1 T2} :
    Γ su⊨ e1 : oAll T1 T2 -∗
    Γ s⊨p pv v2 : T1, 0 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ su⊨ tapp e1 (tv v2) : T2.|[ v2 /].
  Proof.
    iIntros "#H1 #H2"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    iExists (tapp e1s (tv v2)); iSplit; last iApply (sT_All_Ex with "H1").
    done.
    by iApply (sT_Path (p := pv v2)).
  Qed.

  Lemma suT_Obj_E {Γ e T l}:
    Γ su⊨ e : oVMem l T -∗
    Γ su⊨ tproj e l : T.
  Proof.
    iIntros "#H1"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    by iExists (tproj e1s l); iSplit; last iApply (sT_Obj_E with "H1").
  Qed.

  Lemma suT_All_I_Strong {Γ Γ'} T1 T2 e
    (Hctx : s⊨G Γ <:* oLater <$> Γ') :
    shift T1 :: Γ' su⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ su⊨ tv (vabs e) : oAll T1 T2.
  Proof.
    iIntros "#H1"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    by iExists (tv (vabs e1s)); iSplit; last iApply (sT_All_I_Strong with "H1").
  Qed.

  Lemma uT_All_I_Strong {Γ Γ'} T1 T2 e
    (Hctx : ⊨G Γ <:* TLater <$> Γ') :
    shift T1 :: Γ' u⊨ e : T2 -∗
    Γ u⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "#H1"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
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
    iIntros "#H1"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    by iExists (tskip e1s); iSplit; last iApply (sT_Skip with "H1").
  Qed.

  Lemma suT_Sub {Γ e T1 T2}:
    Γ su⊨ e : T1 -∗
    Γ s⊨ T1 <:[0] T2 -∗
    Γ su⊨ e : T2.
  Proof.
    iIntros "#H1 #H2"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    by iExists e1s; iSplit; last iApply (sT_Sub with "H1 H2").
  Qed.


  Lemma suT_Obj_I (Γ : sCtx Σ) (T : clty Σ) ds:
    oLater (c2o T) :: Γ su⊨ds ds : T -∗
    Γ su⊨ tv (vobj ds) : oMu (c2o T).
  Proof.
    iIntros "#H1"; iMod "H1" as (ds1 Hsk1) "H1"; iModIntro.
    by iExists (tv (vobj ds1)); iSplit; last iApply (sT_Obj_I with "H1").
  Qed.

  Lemma suT_Path Γ τ p :
    Γ s⊨p p : τ, 0 -∗ Γ su⊨ path2tm p : τ.
  Proof.
    iIntros "#H1"; iModIntro.
    by iExists (path2tm p); iSplit; last iApply (sT_Path with "H1").
  Qed.
  (* Primitives *)

  Lemma suT_Un Γ u e1 B1 Br (Hu : un_op_semtype u B1 Br) :
    Γ su⊨ e1 : oPrim B1 -∗
    Γ su⊨ tun u e1 : oPrim Br.
  Proof.
    iIntros "#H1"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    by iExists (tun u e1s); iSplit; last iApply (sT_Un with "H1").
  Qed.

  Lemma uT_Un Γ u e1 B1 Br (Hu : un_op_syntype u B1 Br) :
    Γ u⊨ e1 : TPrim B1 -∗
    Γ u⊨ tun u e1 : TPrim Br.
  Proof.
    iIntros "#H1"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    by iExists (tun u e1s); iSplit; last iApply (T_Un with "H1").
  Qed.

  Lemma suT_Bin Γ b e1 e2 B1 B2 Br (Hu : bin_op_semtype b B1 B2 Br (const (const True))) :
    Γ su⊨ e1 : oPrim B1 -∗
    Γ su⊨ e2 : oPrim B2 -∗
    Γ su⊨ tbin b e1 e2 : oPrim Br.
  Proof.
    iIntros "#H1 #H2".
    iMod "H1" as (e1s Hsk1) "H1"; iMod "H2" as (e2s Hsk2) "H2"; iModIntro.
    by iExists (tbin b e1s e2s); iSplit; last iApply (sT_Bin with "H1 H2").
  Qed.

  Lemma uT_Bin Γ b e1 e2 B1 B2 Br (Hu : bin_op_syntype b B1 B2 Br) :
    Γ u⊨ e1 : TPrim B1 -∗
    Γ u⊨ e2 : TPrim B2 -∗
    Γ u⊨ tbin b e1 e2 : TPrim Br.
  Proof.
    iIntros "#H1 #H2".
    iMod "H1" as (e1s Hsk1) "H1"; iMod "H2" as (e2s Hsk2) "H2"; iModIntro.
    by iExists (tbin b e1s e2s); iSplit; last iApply (T_Bin with "H1 H2").
  Qed.

  Lemma suT_If Γ e1 e2 e3 T :
    Γ su⊨ e1 : oBool -∗ Γ su⊨ e2 : T -∗ Γ su⊨ e3 : T -∗
    Γ su⊨ tif e1 e2 e3 : T.
  Proof.
    iIntros "#H1 #H2 #H3".
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
    iIntros "#H1 #H2".
    iMod "H1" as (d1s Hsk1) "H1"; iMod "H2" as (ds2s Hsk2) "H2"; iModIntro.
    iExists ((l, d1s) :: ds2s); iSplit; last iApply (sD_Cons with "H1 H2");
      naive_solver.
  Qed.

  Lemma suD_Sing Γ d l (T : cltyO Σ):
    Γ su⊨ { l := d } : T -∗ Γ su⊨ds [(l, d)] : cAnd T cTop.
  Proof.
    iIntros "#H1"; iMod "H1" as (d1s Hsk1) "H1"; iModIntro.
    by iExists [(l, d1s)]; iSplit; last iApply (sD_Sing with "H1").
  Qed.

  Lemma suD_Val {Γ} T v1 l:
    Γ su⊨ tv v1 : T -∗
    Γ su⊨ { l := dpt (pv v1) } : cVMem l T.
  Proof.
    iIntros "#H1"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    destruct (same_skel_tv_tv Hsk1) as [v1s ->].
    by iExists (dpt (pv v1s)); iSplit; last iApply (sD_Val with "H1").
  Qed.

  Lemma suD_Path {Γ} T p l:
    Γ s⊨p p : T, 0 -∗
    Γ su⊨ { l := dpt p } : cVMem l T.
  Proof.
    iIntros "#H1"; iModIntro.
    by iExists (dpt p); iSplit; last iApply (sD_Path with "H1").
  Qed.

  Lemma suD_Val_New {Γ l ds} {T : clty Σ}:
    oAnd (oLater (c2o T)) (oSing (pself (pv (ids 1)) l)) :: Γ su⊨ds ds : T -∗
    Γ su⊨ { l := dpt (pv (vobj ds)) } : cVMem l (oMu (c2o T)).
  Proof.
    iIntros "#H1"; iMod "H1" as (ds1s Hsk1) "H1"; iModIntro.
    by iExists (dpt (pv (vobj ds1s))); iSplit; last iApply (sD_Val_New with "H1").
  Qed.

  Lemma suD_Path_Stp {Γ T1 T2 p1 l}:
    Γ s⊨ T1 <:[0] T2 -∗
    Γ su⊨ { l := dpt p1 } : cVMem l T1 -∗
    Γ su⊨ { l := dpt p1 } : cVMem l T2.
  Proof.
    iIntros "#Hsub #H1"; iMod "H1" as (d1s Hsk1) "H1"; iModIntro.
    destruct (same_skel_dpt_dpt Hsk1) as [p1s ->].
    by iExists (dpt p1s); iSplit; last iApply (sD_Path_Stp with "Hsub H1").
  Qed.
End unstamped_lemmas.
