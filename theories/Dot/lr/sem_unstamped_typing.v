(** * Unstamped semantic judgments, adequacy, and typing lemmas. *)
From D Require Export iris_prelude swap_later_impl.
From D.pure_program_logic Require Import weakestpre adequacy.
From D Require Import iris_extra.det_reduction.
From D.Dot Require Import skeleton path_repl typing_aux_defs.
From D.Dot Require Import unary_lr.
From D.Dot Require Import later_sub_sem binding_lr path_repl_lr defs_lr dsub_lr prims_lr.
From D.Dot Require Import binding_lr_syn path_repl_lr_syn prims_lr_syn later_sub_syn.
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
    <PB> ∃ e_s, ⌜ same_skel_tm e_u e_s⌝ ∧ Γ s⊨ e_s : T.

  Definition sudstp ds_u Γ T : iProp Σ :=
    <PB> ∃ ds_s, ⌜ same_skel_dms ds_u ds_s⌝ ∧ Γ s⊨ds ds_s : T.

  Definition sudtp l d_u Γ T : iProp Σ :=
    <PB> ∃ d_s, ⌜ same_skel_dm d_u d_s⌝ ∧ Γ s⊨ { l := d_s } : T.

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

#[global] Instance : Params (@suetp) 3 := {}.
#[global] Instance : Params (@sudstp) 3 := {}.
#[global] Instance : Params (@sudtp) 4 := {}.

Ltac rw ::= rewrite /iuetp /ietp /iudstp /idstp /iudtp /idtp /iptp /istpd ?lr.

Section unstamped_judgs_proper.
  Context `{!dlangG Σ}.

  #[global] Instance suetp_proper e : Proper2 (suetp e).
  Proof. rewrite /suetp => ??????. by repeat f_equiv. Qed.

  #[global] Instance sudstp_proper ds : Proper2 (sudstp ds).
  Proof. rewrite /sudstp => ??????; by repeat f_equiv. Qed.

  #[global] Instance sudtp_proper l d : Proper2 (sudtp l d).
  Proof. rewrite /sudtp => ??????. by repeat f_equiv. Qed.
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
  (τ : ∀ `{!dlangG Σ}, olty Σ)
  (Hwp : ∀ `{!dlangG Σ} `(!SwapPropI Σ), ⊢ [] su⊨ e_u : τ) :
  safe e_u.
Proof.
  intros e_u' [n Hsteps]%rtc_nsteps_1.
  apply (soundness (M := iResUR Σ) _ n).
  apply (bupd_plain_soundness _).
  iDestruct (Hwp HdlangG HswapProp) as "#>#(%e_s & %Hsim & -#Hwp)".
  iSpecialize ("Hwp" $! ids with "[//]"); rewrite hsubst_id /=.
  iMod (wptp_safe_n n with "Hwp") as "Hwp".
  iIntros "!>!>"; iRevert "Hwp"; iIntros "!% %Hsafe".
  eapply same_skel_safe_n_impl, Hsteps; naive_solver.
Qed.

(** ** Adequacy of unstamped semantic typing (Theorem 5.4).
semantically well-typed terms are safe. *)
Corollary unstamped_safety_dot_sem Σ `{HdlangG : !dlangG Σ} `{!SwapPropI Σ}
  {e T}
  (Hlog : ∀ `(!dlangG Σ) `(!SwapPropI Σ), ⊢ [] u⊨ e : T) :
  safe e.
Proof. exact: (unstamped_s_safety_dot_sem Σ (λ _, V⟦T⟧)). Qed.

Lemma same_skel_dms_hasnt ds ds' l : dms_hasnt ds l → same_skel_dms ds ds' → dms_hasnt ds' l.
Proof.
  rewrite /dms_hasnt; elim: ds ds' => [| [s d] ds IH] [|[s' d'] ds'] //= ? [<-{s'} ?].
  case_match; naive_solver.
Qed.

#[local] Hint Resolve same_skel_dms_hasnt : core.

Definition coveringσ `{!dlangG Σ} σ (T : olty Σ) : Prop :=
  ∀ args ρ, T args ρ ≡ T args (∞ σ.|[ρ]).

Section coveringσ_intro_lemmas.
  Context `{!dlangG Σ}.

  Lemma nclosed_syn_coveringσ {n} {T : ty} (Hcl : nclosed T n) :
    coveringσ (idsσ n) V⟦T⟧.
  Proof.
    move=> args ρ v /=.
    by rewrite -interp_commute_finsubst_cl ?length_idsσ // closed_subst_idsρ.
  Qed.

  (* Maybe hard to use in general; [nclosed] requires equality on the nose? *)
  Lemma nclosed_sem_coveringσ {n} {T : olty Σ} (Hcl : nclosed T n) :
    coveringσ (idsσ n) T.
  Proof.
    move=> args ρ v.
    by rewrite -olty_finsubst_commute_cl ?length_idsσ // closed_subst_idsρ.
  Qed.

  Lemma coveringσ_shift σ (T : olty Σ) :
    coveringσ σ T → coveringσ (push_var σ) (shift T).
  Proof.
    move => + args ρ => /(_ args (stail ρ)) HclT.
    rewrite /= !olty_weaken_one vls_subst_fold hsubst_comp stail_eq.
    apply HclT.
  Qed.
End coveringσ_intro_lemmas.

Section tmem_unstamped_lemmas.
  Context `{!dlangG Σ}.

  Lemma leadsto_envD_equiv_alloc {σ} {T : olty Σ}
    (Hcl : coveringσ σ T) : ⊢ |==> ∃ s, s ↝[ σ ] T.
  Proof.
    iMod (saved_ho_sem_type_alloc T) as (s) "#Hs"; iIntros "!>".
    iExists s, T; iFrame "Hs"; iIntros "!%". apply Hcl.
  Qed.

  Lemma leadsto_envD_equiv_alloc_shift {σ} {T : olty Σ} :
    coveringσ σ T →
    ⊢ |==> ∃ s, s ↝[ push_var σ ] shift T.
  Proof. intros Hcl; apply leadsto_envD_equiv_alloc, coveringσ_shift, Hcl. Qed.

  Lemma suD_Typ_Gen {l Γ fakeT s σ} {T : olty Σ} :
    s ↝[ σ ] T -∗ Γ su⊨ { l := dtysyn fakeT } : cTMem l (oLater T) (oLater T).
  Proof.
    pupd; iIntros "#Hs !>". iExists (dtysem σ s).
    iSplit; first done; iApply (sD_Typ with "Hs").
  Qed.

  Lemma suD_Typ {l σ Γ fakeT} {T : olty Σ} (HclT : coveringσ σ T) :
    ⊢ Γ su⊨ { l := dtysyn fakeT } : cTMem l (oLater T) (oLater T).
  Proof.
    iModIntro.
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
    pupd; iIntros "#(%d1s & %Hsk1 & H1) !>".
    iExists d1s; iSplit; last done; iIntros "!%".
    apply /same_skel_trans_dm /Hsk1 /same_skel_symm_dm /Hsk.
  Qed.

  Lemma suD_Typ_Stp {Γ} L1 L2 U1 U2 d l :
    Γ s⊨ L2 <:[0] L1 -∗
    Γ s⊨ U1 <:[0] U2 -∗
    Γ su⊨ { l := d } : cTMem l L1 U1 -∗
    Γ su⊨ { l := d } : cTMem l L2 U2.
  Proof.
    pupd; iIntros "#Hsub1 #Hsub2 #(%d1s & %Hsk1 & H1) !>".
    by iExists d1s; iSplit; last iApply (sD_Typ_Stp with "Hsub1 Hsub2 H1").
  Qed.

  Lemma suD_Typ_Abs {l σ Γ L T U} fakeT (HclT : coveringσ σ T) :
    Γ s⊨ L <:[0] oLater T -∗
    Γ s⊨ oLater T <:[0] U -∗
    Γ su⊨ { l := dtysyn fakeT } : cTMem l L U.
  Proof.
    by iIntros "H1 H2"; iApply (suD_Typ_Stp with "H1 H2"); iApply suD_Typ.
  Qed.

  Lemma uD_Typ_Abs {l n Γ L T U} fakeT (HclT : nclosed T n) :
    Γ ⊨ L <:[0] TLater T -∗
    Γ ⊨ TLater T <:[0] U -∗
    Γ u⊨ { l := dtysyn fakeT } : TTMem l L U.
  Proof. have := !!nclosed_syn_coveringσ HclT. rw. apply suD_Typ_Abs. Qed.

  Lemma uD_Typ {l n Γ T} fakeT (HclT : nclosed T n) :
    ⊢ Γ u⊨ { l := dtysyn fakeT } : TTMem l (TLater T) (TLater T).
  Proof. have := !!nclosed_syn_coveringσ HclT. rw. apply suD_Typ. Qed.
End tmem_unstamped_lemmas.

Section unstamped_lemmas.
  Context `{!dlangG Σ}.

  Lemma suT_All_E {Γ e1 e2 T1 T2} :
    Γ su⊨ e1 : oAll T1 (shift T2) -∗
    Γ su⊨ e2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ su⊨ tapp e1 e2 : T2.
  Proof.
    pupd; iIntros "#(%e1s & %Hsk1 & H1) #(%e2s & %Hsk2 & H2) !>".
    by iExists (tapp e1s e2s); iSplit; last iApply (sT_All_E with "H1 H2").
  Qed.

  Lemma uT_All_E {Γ e1 e2 T1 T2} :
    Γ u⊨ e1 : TAll T1 (shift T2) -∗ Γ u⊨ e2 : T1 -∗ Γ u⊨ tapp e1 e2 : T2.
  Proof.
    pupd; iIntros "#(%e1s & %Hsk1 & H1) #(%e2s & %Hsk2 & H2) !>".
    by iExists (tapp e1s e2s); iSplit; last iApply (T_All_E with "H1 H2").
  Qed.

  Lemma suT_All_E_p {Γ e1 p2 T1 T2} :
    Γ su⊨ e1 : oAll T1 T2 -∗
    Γ s⊨p p2 : T1, 0 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ su⊨ tapp e1 (path2tm p2) : T2 .sTp[ p2 /].
  Proof.
    pupd; iIntros "#(%e1s & %Hsk1 & H1) #H2 !>".
    by iExists (tapp e1s (path2tm p2)); iSplit; last iApply (sT_All_E_p with "H1 H2").
  Qed.

  Lemma uT_All_E_p Γ e1 p2 T1 T2 T2' (Hrepl : T2 .Tp[ p2 /]~ T2') :
    Γ u⊨ e1 : TAll T1 T2 -∗
    Γ ⊨p p2 : T1, 0 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ u⊨ tapp e1 (path2tm p2) : T2'.
  Proof.
    pupd; iIntros "#(%e1s & %Hsk1 & H1) #H2 !>".
    by iExists (tapp e1s (path2tm p2)); iSplit; last iApply (T_All_E_p with "H1 H2").
  Qed.

  Lemma suT_All_Ex {Γ e1 v2 T1 T2} :
    Γ su⊨ e1 : oAll T1 T2 -∗
    Γ s⊨p pv v2 : T1, 0 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ su⊨ tapp e1 (tv v2) : T2.|[ v2 /].
  Proof.
    pupd; iIntros "#(%e1s & %Hsk1 & H1) #H2 !>".
    iExists (tapp e1s (tv v2)); iSplit; last iApply (sT_All_Ex with "H1").
    done.
    by iApply (sT_Path (p := pv v2)).
  Qed.

  Lemma suT_Obj_E {Γ e T l} :
    Γ su⊨ e : oVMem l T -∗
    Γ su⊨ tproj e l : T.
  Proof.
    pupd; iIntros "#(%e1s & %Hsk1 & H1) !>".
    by iExists (tproj e1s l); iSplit; last iApply (sT_Obj_E with "H1").
  Qed.

  Lemma uT_Obj_E {Γ e T l} :
    Γ u⊨ e : TVMem l T -∗
    Γ u⊨ tproj e l : T.
  Proof. rw. apply suT_Obj_E. Qed.

  Lemma suT_All_I_Strong {Γ Γ'} T1 T2 e
    (Hctx : s⊨G Γ <:* oLater <$> Γ') :
    shift T1 :: Γ' su⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ su⊨ tv (vabs e) : oAll T1 T2.
  Proof.
    pupd; iIntros "#(%e1s & %Hsk1 & H1) !>".
    by iExists (tv (vabs e1s)); iSplit; last iApply (sT_All_I_Strong with "H1").
  Qed.

  Lemma uT_All_I_Strong {Γ Γ'} T1 T2 e
    (Hctx : ⊨G Γ <:* TLater <$> Γ') :
    shift T1 :: Γ' u⊨ e : T2 -∗
    Γ u⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    pupd; iIntros "#(%e1s & %Hsk1 & H1) !>".
    by iExists (tv (vabs e1s)); iSplit; last iApply (T_All_I_Strong with "H1").
  Qed.

  Lemma suT_All_I {Γ} T1 T2 e :
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
    pupd; iIntros "#(%e1s & %Hsk1 & H1) !>".
    by iExists (tskip e1s); iSplit; last iApply (sT_Skip with "H1").
  Qed.

  Lemma uT_Skip Γ e T :
    Γ u⊨ e : TLater T -∗
    Γ u⊨ tskip e : T.
  Proof. rw. apply suT_Skip. Qed.

  Lemma suT_Sub {Γ e T1 T2} :
    Γ su⊨ e : T1 -∗
    Γ s⊨ T1 <:[0] T2 -∗
    Γ su⊨ e : T2.
  Proof.
    pupd; iIntros "#(%e1s & %Hsk1 & H1) #H2 !>".
    by iExists e1s; iSplit; last iApply (sT_Sub with "H1 H2").
  Qed.

  Lemma uT_Sub {Γ e T1 T2} :
    Γ u⊨ e : T1 -∗
    Γ ⊨ T1 <:[0] T2 -∗
    Γ u⊨ e : T2.
  Proof. apply suT_Sub. Qed.

  Lemma suT_Obj_I (Γ : sCtx Σ) (T : clty Σ) ds :
    oLater T :: Γ su⊨ds ds : T -∗
    Γ su⊨ tv (vobj ds) : oMu T.
  Proof.
    pupd; iIntros "#(%ds1s & %Hsk1 & H1) !>".
    by iExists (tv (vobj ds1s)); iSplit; last iApply (sT_Obj_I with "H1").
  Qed.

  Lemma uT_Obj_I Γ T ds :
    TLater T :: Γ u⊨ds ds : T -∗
    Γ u⊨ tv (vobj ds) : TMu T.
  Proof. rw. apply suT_Obj_I. Qed.

  Lemma suT_Path Γ τ p :
    Γ s⊨p p : τ, 0 -∗ Γ su⊨ path2tm p : τ.
  Proof.
    pupd; iIntros "#H1 !>".
    by iExists (path2tm p); iSplit; last iApply (sT_Path with "H1").
  Qed.
  (* Primitives *)

  Lemma suT_Un Γ u e1 B1 Br (Hu : un_op_semtype u B1 Br) :
    Γ su⊨ e1 : oPrim B1 -∗
    Γ su⊨ tun u e1 : oPrim Br.
  Proof.
    pupd; iIntros "#(%e1s & %Hsk1 & H1) !>".
    by iExists (tun u e1s); iSplit; last iApply (sT_Un with "H1").
  Qed.

  Lemma uT_Un Γ u e1 B1 Br (Hu : un_op_syntype u B1 Br) :
    Γ u⊨ e1 : TPrim B1 -∗
    Γ u⊨ tun u e1 : TPrim Br.
  Proof.
    pupd; iIntros "#(%e1s & %Hsk1 & H1) !>".
    by iExists (tun u e1s); iSplit; last iApply (T_Un with "H1").
  Qed.

  Lemma suT_Bin Γ b e1 e2 B1 B2 Br (Hu : bin_op_semtype b B1 B2 Br (const (const True))) :
    Γ su⊨ e1 : oPrim B1 -∗
    Γ su⊨ e2 : oPrim B2 -∗
    Γ su⊨ tbin b e1 e2 : oPrim Br.
  Proof.
    pupd; iIntros "#(%e1s & %Hsk1 & H1) #(%e2s & %Hsk2 & H2) !>".
    by iExists (tbin b e1s e2s); iSplit; last iApply (sT_Bin with "H1 H2").
  Qed.

  Lemma uT_Bin Γ b e1 e2 B1 B2 Br (Hu : bin_op_syntype b B1 B2 Br) :
    Γ u⊨ e1 : TPrim B1 -∗
    Γ u⊨ e2 : TPrim B2 -∗
    Γ u⊨ tbin b e1 e2 : TPrim Br.
  Proof.
    pupd; iIntros "#(%e1s & %Hsk1 & H1) #(%e2s & %Hsk2 & H2) !>".
    by iExists (tbin b e1s e2s); iSplit; last iApply (T_Bin with "H1 H2").
  Qed.

  Lemma suT_If Γ e1 e2 e3 T :
    Γ su⊨ e1 : oBool -∗ Γ su⊨ e2 : T -∗ Γ su⊨ e3 : T -∗
    Γ su⊨ tif e1 e2 e3 : T.
  Proof.
    pupd; iIntros "#(%e1s & %Hsk1 & H1) #(%e2s & %Hsk2 & H2) #(%e3s & %Hsk3 & H3) !>".
    by iExists (tif e1s e2s e3s); iSplit; last iApply (sT_If with "H1 H2 H3").
  Qed.

  Lemma uT_If Γ e1 e2 e3 T :
    Γ u⊨ e1 : TBool -∗ Γ u⊨ e2 : T -∗ Γ u⊨ e3 : T -∗
    Γ u⊨ tif e1 e2 e3 : T.
  Proof. rw. apply suT_If. Qed.

  Lemma suD_Nil Γ : ⊢ Γ su⊨ds [] : cTop.
  Proof. iExists []. by rewrite -sD_Nil. Qed.

  Lemma uD_Nil Γ : ⊢ Γ u⊨ds [] : TTop.
  Proof. rw. apply suD_Nil. Qed.

  Lemma suD_Cons Γ d1 ds2 l (T1 T2 : cltyO Σ)
    (Hlds : dms_hasnt ds2 l) :
    Γ su⊨ { l := d1 } : T1 -∗ Γ su⊨ds ds2 : T2 -∗
    Γ su⊨ds (l, d1) :: ds2 : cAnd T1 T2.
  Proof.
    pupd; iIntros "#(%d1s & %Hsk1 & H1) #(%ds2s & %Hsk2 & H2) !>".
    iExists ((l, d1s) :: ds2s); iSplit; last iApply (sD_Cons with "H1 H2");
      naive_solver.
  Qed.

  Lemma uD_Cons Γ d1 ds2 l T1 T2
    (Hlds : dms_hasnt ds2 l) :
    Γ u⊨ { l := d1 } : T1 -∗ Γ u⊨ds ds2 : T2 -∗
    Γ u⊨ds (l, d1) :: ds2 : TAnd T1 T2.
  Proof. rw. exact: suD_Cons. Qed.

  Lemma suD_Sing Γ d l (T : cltyO Σ) :
    Γ su⊨ { l := d } : T -∗ Γ su⊨ds [(l, d)] : cAnd T cTop.
  Proof.
    pupd; iIntros "#(%d1s & %Hsk1 & H1) !>".
    by iExists [(l, d1s)]; iSplit; last iApply (sD_Sing with "H1").
  Qed.

  Lemma uD_Sing Γ d l T :
    Γ u⊨ { l := d } : T -∗ Γ u⊨ds [(l, d)] : TAnd T TTop.
  Proof. rw. apply suD_Sing. Qed.

  Lemma suD_Val {Γ} T v1 l :
    Γ su⊨ tv v1 : T -∗
    Γ su⊨ { l := dpt (pv v1) } : cVMem l T.
  Proof.
    pupd; iIntros "#(%e1s & %Hsk1 & H1) !>".
    destruct (same_skel_tv_tv Hsk1) as [v1s ->].
    by iExists (dpt (pv v1s)); iSplit; last iApply (sD_Val with "H1").
  Qed.

  Lemma uD_Val {Γ} T v1 l :
    Γ u⊨ tv v1 : T -∗
    Γ u⊨ { l := dpt (pv v1) } : TVMem l T.
  Proof. rw. apply suD_Val. Qed.

  Lemma suD_Path {Γ} T p l :
    Γ s⊨p p : T, 0 -∗
    Γ su⊨ { l := dpt p } : cVMem l T.
  Proof.
    pupd; iIntros "#H1 !>".
    by iExists (dpt p); iSplit; last iApply (sD_Path with "H1").
  Qed.

  Lemma uD_Path {Γ} T p l :
    Γ ⊨p p : T, 0 -∗
    Γ u⊨ { l := dpt p } : TVMem l T.
  Proof. rw. apply suD_Path. Qed.

  Lemma suD_Val_New {Γ l ds} {T : clty Σ} :
    oAnd (oLater T) (oSing (pself (pv (ids 1)) l)) :: Γ su⊨ds ds : T -∗
    Γ su⊨ { l := dpt (pv (vobj ds)) } : cVMem l (oMu T).
  Proof.
    pupd; iIntros "#(%ds1s & %Hsk1 & H1) !>".
    by iExists (dpt (pv (vobj ds1s))); iSplit; last iApply (sD_Val_New with "H1").
  Qed.

  Lemma uD_Val_New {Γ l ds} T :
    TAnd (TLater T) (TSing (pself (pv (ids 1)) l)) :: Γ u⊨ds ds : T -∗
    Γ u⊨ { l := dpt (pv (vobj ds)) } : TVMem l (TMu T).
  Proof. rw. apply suD_Val_New. Qed.

  Lemma suD_Path_Stp {Γ T1 T2 p1 l} :
    Γ s⊨ T1 <:[0] T2 -∗
    Γ su⊨ { l := dpt p1 } : cVMem l T1 -∗
    Γ su⊨ { l := dpt p1 } : cVMem l T2.
  Proof.
    pupd; iIntros "#Hsub #(%d1s & %Hsk1 & H1) !>".
    destruct (same_skel_dpt_dpt Hsk1) as [p1s ->].
    by iExists (dpt p1s); iSplit; last iApply (sD_Path_Stp with "Hsub H1").
  Qed.

  Lemma uD_Path_Stp {Γ T1 T2 p1 l}:
    Γ ⊨ T1 <:[0] T2 -∗
    Γ u⊨ { l := dpt p1 } : TVMem l T1 -∗
    Γ u⊨ { l := dpt p1 } : TVMem l T2.
  Proof. rw. apply suD_Path_Stp. Qed.
End unstamped_lemmas.
