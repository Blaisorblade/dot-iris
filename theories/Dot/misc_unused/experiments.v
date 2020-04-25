From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language ectx_language ectxi_language.
From iris.proofmode Require Import tactics.
From D Require Import swap_later_impl.
From D.Dot Require Import syn_lemmas rules path_repl.
From D.Dot Require Import typing_aux_defs.
From D.Dot Require Import unary_lr
  binding_lr tsel_lr no_binding_lr defs_lr path_repl_lr later_sub_sem.

Implicit Types
         (v: vl) (e: tm) (d: dm) (ds: dms) (p : path).

Set Suggest Proof Using.
Set Default Proof Using "Type".

Section NoSwapVariants.
  Context `{HdlangG: !dlangG Σ}.

  (* Yes, no swap! *)
  Lemma sTyp_Sub_Typ {Γ L1 L2 U1 U2 l}:
    Γ s⊨ oLater L2, 0 <: oLater L1, 0 -∗
    Γ s⊨ oLater U1, 0 <: oLater U2, 0 -∗
    Γ s⊨ cTMem l L1 U1, 0 <: cTMem l L2 U2, 0.
  Proof using HdlangG.
    iIntros "#IHT #IHT1 /= !>" (ρ v) "#Hg #HT1".
    iDestruct "HT1" as (d) "[Hl2 H]".
    iDestruct "H" as (φ) "#[Hφl [HLφ #HφU]]".
    iExists d; repeat iSplit; first by [].
    iExists φ; repeat iSplitL; first by [];
      rewrite -?mlater_pers;
      iIntros "!>" (w);
      iSpecialize ("IHT" $! ρ w with "Hg");
      iSpecialize ("IHT1" $! ρ w with "Hg");
      iIntros.
    - iApply "HLφ" => //. by iApply "IHT".
    - iApply "IHT1". by iApply "HφU".
  Qed.

  Context `{HswapProp : !SwapPropI Σ}.
  (* A swap still needed, but only because functions are contractive. *)
  Lemma sAll_Sub_All {Γ T1 T2 U1 U2}:
    Γ s⊨ oLater T2, 0 <: oLater T1, 0 -∗
    oLater (shift T2) :: Γ s⊨ oLater U1, 0 <: oLater U2, 0 -∗
    Γ s⊨ oAll T1 U1, 0 <: oAll T2 U2, 0.
  Proof using HdlangG HswapProp.
    iIntros "#HsubT #HsubU /= !>" (ρ v) "#Hg #HT1".
    iDestruct "HT1" as (t) "#[Heq #HT1]". iExists t; iSplit => //.
    iIntros (w).
    (* rewrite -mlater_impl. *)
    iIntros "!> #HwT2".
    iSpecialize ("HsubT" $! ρ w with "Hg HwT2").
    iSpecialize ("HsubU" $! (w .: ρ)); iEval (rewrite -forall_swap_impl) in "HsubU".
    iSpecialize ("HsubU" with "[# $Hg]").
    by iApply hoEnvD_weaken_one.
    setoid_rewrite mlater_impl.
    rewrite -!mlater_pers; iModIntro.
    iNext 1.
    iApply wp_wand.
    - iApply ("HT1" with "[]"). iApply "HsubT".
    - iIntros (u) "#HuU1". by iApply "HsubU".
  Qed.
End NoSwapVariants.

(** These typing lemmas can be derived syntactically.
 But I had written semantic proofs first, and they might help. *)
Section AlsoSyntactically.
  Context `{HdlangG: !dlangG Σ}.

  (* Also derivable syntactically. *)
  Lemma singleton_Mu_1 {Γ p T i T'} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : TMu T, i -∗
    Γ ⊨ TSing p, i <: T', i.
  Proof. rewrite (P_Mu_E Hrepl). apply Sngl_Sub_Self. Qed.

  Lemma singleton_Mu_2 {Γ p T i T'} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : T', i -∗
    Γ ⊨ TSing p, i <: TMu T, i.
  Proof. rewrite (P_Mu_I Hrepl). apply Sngl_Sub_Self. Qed.

  (** Semantic version of derived rule [singleton_Mu_dotty1]. *)
  Lemma singleton_Mu_dotty1 {Γ p i T1 T2 T2'}
    (Hrepl2 : T2 .Tp[ p /]~ T2'):
    Γ ⊨ T1, i <: T2', i -∗
    Γ ⊨p p : T1, i -∗
    Γ ⊨ TSing p, i <: TMu T2, i.
  Proof.
    (* iIntros "#Hsub #Hp !>" (ρ v) "#Hg /= #Heq".
    iSpecialize ("Hp" with "Hg").
    iSpecialize ("Hsub" $! ρ v with "[#$Hg] [#]");
      iNext i; iDestruct "Heq" as %Heq;
      rewrite (alias_paths_elim_eq _ Heq) // -(psubst_one_repl Hrepl2) //.
    Restart. *)
    iIntros "Hsub Hp".
    iApply (singleton_Mu_2 Hrepl2).
    iApply (sP_Sub' with "Hp Hsub").
  Qed.

End AlsoSyntactically.

(* Additional typing lemmas that *)
Section NotUsed.
  Context `{HdlangG: !dlangG Σ}.

  (* Derivable *)
  Lemma T_All_I {Γ} T1 T2 e:
    shift T1 :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof. rewrite -(T_All_I_Strong (Γ := Γ)) //. ietp_weaken_ctx. Qed.
End NotUsed.

From D.Dot Require ex_utils storeless_typing_ex_utils.
From D.Dot Require fundamental typing_stamping.
From D.Dot.examples Require scala_lib.

Import fundamental.

Section Example.
  Context `{HdlangG: !dlangG Σ} `{SwapPropI Σ}.
  Set Default Proof Using "Type*".
  Import ex_utils storeless_typing_ex_utils fundamental typing_stamping scala_lib.

  Lemma OrSplit Γ e1 e2 A B C :
    Γ ⊨ e1 : TOr A B -∗
    shift A :: Γ ⊨ e2 : shift C -∗
    shift B :: Γ ⊨ e2 : shift C -∗
    Γ ⊨ lett e1 e2 : C.
  Proof.
    iIntros "He #HA #HB".
    iApply (T_All_E with "[] He").
    iApply T_All_I.
    iSimpl; iIntros "!>" (ρ) "#[Hg [H|H]] !>";
      [iApply ("HA" with "[]") | iApply ("HB" with "[]")];
      iFrame "Hg H".
  Qed.
End Example.

Section Sec.
  Context `{HdlangG: !dlangG Σ}.

  Lemma T_later_ctx Γ V T e:
    TLater <$> (V :: Γ) ⊨ e : T -∗
    (*─────────────────────────*)
    TLater V :: Γ ⊨ e : T.
  Proof. by rewrite fmap_cons -(ctx_sub_TLater Γ). Qed.

  (* Variant of [P_Fld_I]: not needed here, and we get an extra later :-|, tho it
  matches [T_Obj_E']. Fails now that we allow path members, and it
  always required inverting WP. *)
  (* Lemma T_Mem_I Γ e T l:
    Γ ⊨ tproj e l : T -∗
    (*─────────────────────────*)
    Γ ⊨ e : TVMem l (TLater T). *)

  Lemma All_Later_Sub_Distr0 Γ T U `{SwapPropI Σ}:
    ⊢ Γ ⊨ TAll (TLater T) U, 0 <: TLater (TAll T U), 0.
  Proof.
    iIntros "!>" (ρ v) "_ /= #HvTU".
    iDestruct "HvTU" as (t ->) "#HvTU".
    iExists t; iSplit => //. iNext.
    iIntros (w) "!>".
    iIntros "#HwT".
    by iApply ("HvTU" with "[# $HwT]").
  Qed.

  Lemma T_Path' i Γ T p :
    Γ ⊨p p : iterate TLater i T, 0 -∗
    Γ ⊨ iterate tskip i (path2tm p) : T.
  Proof.
    rewrite T_Path.
    iIntros "Hp". iApply (T_Sub with "Hp").
    iIntros "!> **"; by rewrite iterate_TLater_later.
  Qed.

  Lemma wp_later_swap t Φ: WP t {{ v, ▷ Φ v }} ⊢ ▷ WP t {{ v, Φ v }}.
  Proof.
    iLöb as "IH" forall (t Φ).
    iEval (rewrite !wp_unfold /wp_pre /=).
    case: (to_val t) => [v|]. by eauto.
    iDestruct 1 as (e2 Hstep) "H".
    iExists e2; iSplit; first done.
    iApply ("IH" with "H").
  Qed.

  Lemma T_All_I'' Γ T1 T2 e :
    TLater (shift T1) :: Γ ⊨ e : TLater T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "/= #HeT !>" (vs) "#HG !>".
    rewrite -wp_value'. iExists _; iSplit; first done.
    iIntros "!>" (v) "#Hv"; rewrite up_sub_compose /=.
    (* iApply (wp_later_swap _ (⟦ T2 ⟧ (v .: vs))).
    iApply ("HeT" $! (v .: vs) with "[$HG]"). *)
    iSpecialize ("HeT" $! (v .: vs) with "[#$HG]").
    by rewrite (interp_weaken_one _ _ _).
    by rewrite wp_later_swap; iNext.
    (* by iDestruct (wp_later_swap with "HeT") as "{HeT} HeT"; iNext. *)
  Qed.

  (** Stronger version of All_Later_Sub_Distr0, needs wp_later_swap, which
      might not extend to stronger WPs?*)
  Lemma All_Later_Sub_Distr `{SwapPropI Σ} Γ T U i:
    ⊢ Γ ⊨ TAll (TLater T) (TLater U), i <: TLater (TAll T U), i.
  Proof.
    iIntros "!>" (ρ v) "_ #HvTU". iNext i.
    iDestruct "HvTU" as (t ->) "#HvTU".
    iExists t; iSplit => //.
    rewrite -mlater_pers. iModIntro (□ _)%I.
    iIntros (w). iSpecialize ("HvTU" $! w).
    rewrite /= !later_intuitionistically -impl_later later_intuitionistically.
    rewrite (wp_later_swap _ (V⟦ _ ⟧ _ _)).
    (* Either: *)
    done.
    (* Or keep the old but more flexible code: *)
    (* iIntros "#HwT".
    iApply ("HvTU" with "HwT"). *)
  Qed.

  Lemma Fld_Later_Sub_Distr Γ l T i:
    ⊢ Γ ⊨ TVMem l (TLater T), i <: TLater (TVMem l T), i.
  Proof.
    iIntros "!>" (ρ v) "_ /= #HvT". iNext i.
    iDestruct "HvT" as (d Hlook) "#HvT".
    iExists (d); (iSplit; try iSplit) => //.
    iDestruct "HvT" as (pmem ->) "HvT".
    rewrite path_wp_later_swap.
    iExists (pmem); by iSplit.
  Qed.

  Lemma sSub_Mono Γ T i :
    ⊢ Γ s⊨ T, i <: T, S i.
  Proof. by iIntros "!> **". Qed.

  (** Rename. *)
  Lemma iterate_Sub_Mono Γ T i j:
    ⊢ Γ ⊨ T, i <: T, j + i.
  Proof.
    iInduction j as [] "IHj".
    - iApply Sub_Refl.
    - iApply (Sub_Trans with "IHj").
      iApply sSub_Mono.
  Qed.

  Lemma iterate_Sub_Later Γ T i j:
    ⊢ Γ ⊨ T, j + i <: iterate TLater j T, i.
  Proof.
      iInduction j as [] "IHj" forall (T).
    - iApply Sub_Refl.
    - iApply (Sub_Trans (i2 := j + i) (T2 := TLater T)); rewrite ?iterate_Sr /=.
      + iApply sSub_Later.
      + iApply ("IHj" $! (TLater T)).
  Qed.

  Lemma Distr_TLater_And T1 T2 args ρ v:
    V⟦ TLater (TAnd T1 T2) ⟧ args ρ v ⊣⊢
    V⟦ TAnd (TLater T1) (TLater T2) ⟧ args ρ v.
  Proof. iSplit; iIntros "/= [$ $]". Qed.

  Lemma selfIntersect Γ T U i j:
    Γ ⊨ T, i <: U, j + i -∗
    Γ ⊨ T, i <: TAnd U T, j + i .
  Proof.
    iIntros "H"; iApply (sSub_And with "[H//] []").
    iApply iterate_Sub_Mono.
  Qed.

  Lemma selfIntersectLater Γ T U i:
    Γ ⊨ T, i <: TLater U, i -∗
    Γ ⊨ T, i <: TLater (TAnd T U), i .
  Proof.
    rewrite /istpi.
    iIntros "H"; iSimpl; setoid_rewrite Distr_TLater_And.
    iApply (sSub_And _ _ (oLater _) with "[] H").
    iApply (sSub_Trans (i2 := S i)).
    - by iApply sSub_Mono.
    - by iApply sSub_Later.
  Qed.

  Lemma Distr_TLaterN_And T1 T2 j args ρ v:
    V⟦ iterate TLater j (TAnd T1 T2) ⟧ args ρ v ⊣⊢
    V⟦ TAnd (iterate TLater j T1) (iterate TLater j T2) ⟧ args ρ v.
  Proof.
    rewrite /= !iterate_TLater_later /=.
    iSplit; iIntros "/= [??]"; iSplit; by [].
  Qed.

  Lemma sub_rewrite_2 Γ T U1 U2 i:
    (∀ args ρ v, V⟦ U1 ⟧ args ρ v ⊣⊢ V⟦ U2 ⟧ args ρ v) →
    Γ ⊨ T, i <: U1, i ⊣⊢
    Γ ⊨ T, i <: U2, i .
  Proof.
    iIntros (Heq); iSplit; iIntros "/= #H !>" (ρ v) "#Hg #HT";
      [rewrite -Heq //|rewrite Heq //]; by iApply "H".
  Qed.

  Lemma sub_rewrite_1 Γ T1 T2 U i:
    (∀ args ρ v, V⟦ T1 ⟧ args ρ v ⊣⊢ V⟦ T2 ⟧ args ρ v) →
    Γ ⊨ T1, i <: U, i ⊣⊢
    Γ ⊨ T2, i <: U, i .
  Proof.
    iIntros (Heq); iSplit; iIntros "/= #H !>" (ρ v) "#Hg #HT";
      [rewrite -Heq //|rewrite Heq //]; by iApply "H".
  Qed.

  Lemma eq_to_bisub Γ T1 T2 i:
    (∀ args ρ v, V⟦ T1 ⟧ args ρ v ⊣⊢ V⟦ T2 ⟧ args ρ v) → True ⊢
    Γ ⊨ T1, i <: T2, i ∧
    Γ ⊨ T2, i <: T1, i .
  Proof.
    iIntros (Heq) "_"; iSplit; iIntros "/= !>" (ρ v) "#Hg #HT";
      [rewrite -Heq //|rewrite Heq //]; by iApply "H".
  Qed.

  Lemma selfIntersectLaterN Γ T U i j:
    Γ ⊨ T, i <: iterate TLater j U, i -∗
    Γ ⊨ T, i <: iterate TLater j (TAnd T U), i .
  Proof.
    iIntros "H".
    setoid_rewrite (sub_rewrite_2 Γ T _ _ i (Distr_TLaterN_And T U j)).
    iApply (sSub_And with "[] H").
    iApply (Sub_Trans (T2 := T) (i2 :=  j + i)).
    - by iApply iterate_Sub_Mono.
    - by iApply iterate_Sub_Later.
  Qed.

  Lemma iterate_Later_Sub Γ T i j:
    ⊢ Γ ⊨ iterate TLater j T, i <: T, i + j.
  Proof.
      iInduction j as [] "IHj" forall (T); rewrite ?plusnO ?iterate_Sr ?plusnS.
    - iApply Sub_Refl.
    - iApply Sub_Trans.
      iApply ("IHj" $! (TLater T)).
      iApply sLater_Sub.
  Qed.

  (* The point is, ensuring this works with T being a singleton type :-) *)
  Lemma dropLaters Γ e T U i:
    Γ ⊨ e : T -∗ Γ ⊨ T, 0 <: iterate TLater i U, 0 -∗
    Γ ⊨ iterate tskip i e : TAnd T U.
  Proof.
    iIntros "HeT Hsub".
    iApply (T_Sub with "HeT [Hsub]").
    iApply (Sub_Trans with "[-]").
    - by iApply selfIntersectLaterN.
    - iApply (iterate_Later_Sub _ _ 0 i).
  Qed.

  (* Exercise: do this with only *syntactic* typing rules. *)
End Sec.
