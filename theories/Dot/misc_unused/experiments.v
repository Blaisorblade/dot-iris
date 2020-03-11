From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language ectx_language ectxi_language.
From iris.proofmode Require Import tactics.
From D Require Import swap_later_impl.
From D.Dot.syn Require Import synLemmas rules path_repl.
From D.Dot Require Import typing_aux_defs.
From D.Dot.lr Require Import unary_lr
  lr_lemmas lr_lemmasTSel lr_lemmasNoBinding lr_lemmasDefs path_repl later_sub_sem.

Implicit Types
         (v: vl) (e: tm) (d: dm) (ds: dms) (p : path).

Set Suggest Proof Using.
Set Default Proof Using "Type".

Section NoSwapVariants.
  Context `{HdlangG: dlangG Σ}.

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
  Context `{HdlangG: dlangG Σ}.

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
  Context `{HdlangG: dlangG Σ}.

  (* Derivable *)
  Lemma T_All_I {Γ} T1 T2 e:
    shift T1 :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof. rewrite -(T_All_I_Strong (Γ := Γ)) //. ietp_weaken_ctx. Qed.
End NotUsed.

From D.Dot Require exampleInfra typingExInfra.
From D.Dot Require fundamental typingStamping.
From D.Dot.examples Require scalaLib.

Import fundamental.

Section Example.
  Context `{HdlangG: dlangG Σ} `{SwapPropI Σ}.
  Set Default Proof Using "Type*".
  Import exampleInfra typingExInfra fundamental typingStamping scalaLib.

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

  Definition iftFalse := (∀: tparam "A", (∀: p0 @; "A", (∀: p1 @; "A", TSing p0)))%ty.
  Definition s0 := 1%positive.
  Definition g0 s T : stys := <[ s := T ]>∅.

  Import stamp_transfer astStamping.

  Lemma wellMappedφ_g0 s T:
    s ↝n[ 0 ] V⟦ T ⟧ -∗
    wellMappedφ (Vs⟦ g0 s T ⟧).
  Proof.
    iIntros "Hs"; rewrite fmap_insert.
    iApply (wellMappedφ_insert with "[] Hs"); iApply wellMappedφ_empty.
  Qed.

  Definition applyE e v1 v2 := e $: tv (packTV 0 s0) $: tv v1 $: tv v2.

  (* XXX "only empty context" won't be enough :-( *)
  Example foo1 s T (Hcl : nclosed T 0) :
    s ↝n[ 0 ] V⟦ T ⟧ -∗
    (* Γ ⊨ tv (packTV (length Γ) s) : typeEq "A" T. *)
    [] ⊨ tv (packTV 0 s) : typeEq "A" T.
  Proof.
    iIntros "#Hs !>" (ρ) "#_ /= !>".
    rewrite -wp_value'.
    iExists (dtysem [] s); iSplit; first eauto.
    iExists (hoEnvD_inst [] V⟦ T ⟧); iSplit; first by iApply dm_to_type_intro.
    iModIntro; iSplit; iIntros (v) "#H !>";
      by rewrite (interp_subst_ids T ρ v) (closed_subst_id _ Hcl).
  Qed.

  (* XXX use more semantic typing. *)
  Example packTV_semTyped Γ s T (Hu: is_unstamped_ty' (length Γ) T):
    s ↝n[ 0 ] V⟦ T ⟧ -∗
    Γ ⊨ tv (packTV (length Γ) s) : typeEq "A" T.
    (* Γ ⊨ tv (packTV (length Γ) s) : type "A" >: ⊥ <: T. *)
  Proof.
    (* iIntros "#Hs !>" (ρ) "#Hg /=".
    rewrite -wp_value'.
    iExists (dtysem _ s); iSplit; first eauto.
    iExists (⟦ T ⟧ ρ); iSplit.
    rewrite hsubst_comp.
    Transparent dm_to_type stamp_σ_to_type_n.
    iExists s, _; iSplit; first done.
    iExists (λ _, ⟦ T ⟧); iSplit; first done.
    iPureIntro; rewrite /= /vopen => _ v.
    asimpl.
    From D.Dot Require unstampedness_binding.
    have ?: nclosed T (length Γ) by eauto.
    by rewrite -interp_finsubst_commute_cl ?length_idsσ ?closed_subst_idsρ.
    eauto 10.
    Restart. *)
    iIntros "#Hs".
    (* iAssert (wellMappedφ (Vs⟦ <[ s := T ]>∅ ⟧)) as "#Hw". *)
    iApply fundamental_typed; last by iApply (wellMappedφ_g0 with "Hs").
    have Hst: is_stamped_ty (length Γ) (<[s:=T]> ∅) T.
    exact: unstamped_stamped_type.
    (* eapply iT_Sub_nocoerce. *)
    eapply packTV_typed'; rewrite //= ?lookup_insert //.
    (* tcrush. *)
  Qed.
    (* Unshelve.
    done.
    apply typing_obj_ident_to_typing.

    rewrite -(iterate_0 tskip (tv _)).
    iApply (T_Sub _ _ ((μ {@ typeEq "A" (shift T) }))); first last.
    iApply Sub_Bind_1; rewrite iterate_0.
    iApply Sub_Trans. iApply
    iApply T_Obj_I.
  Qed. *)

  Example foo e v1 v2:
    s0 ↝n[ 0 ] V⟦ ⊤%ty ⟧ -∗
    [] ⊨ e : iftFalse -∗
    [] ⊨ tv v1 : TTop -∗
    [] ⊨ tv v2 : TTop -∗
    [] ⊨ applyE e v1 v2 : TSing (pv v2).
  Proof.
    rewrite /iftFalse.
    iIntros "#Hs #He #Hv1 #Hv2".
    iAssert ([] ⊨ ⊤, 0 <: pv (packTV 0 s0) @; "A", 0) as "#Hsub". {
      iApply (Sub_Trans (T2 := ▶: ⊤) (i2 := 0)).
      iApply sSub_Add_Later.
      iApply Sub_Sel.
      iApply P_Val.
      iApply (packTV_semTyped with "Hs"); stcrush.
    }
    Arguments T_All_Ex {_ _ _ _ _ _ _}.
    iApply (T_All_Ex (v2 := v2) (T1 := pv (packTV 0 s0) @; "A") (T2 := TSing p0)); first last.
    iApply (T_Sub (i := 0) with "Hv2 Hsub").
    iApply T_All_E; first last.
    iApply (T_Sub (i := 0) with "Hv1 Hsub").
    Timeout 1 iApply (T_All_Ex (v2 := packTV 0 s0) with "He").
    iApply (T_Sub (T1 := typeEq "A" ⊤) (i := 0)).
    iApply (packTV_semTyped [] with "Hs"); stcrush.
    iApply (fundamental_subtype _ ∅); last iApply wellMappedφ_empty.
    tcrush.
  Qed.

  Example foosyn Γ e v1 v2:
    let g := g0 s0 ⊤ in
    Γ v⊢ₜ[ g ] e : iftFalse →
    Γ v⊢ₜ[ g ] tv v1 : TTop →
    Γ v⊢ₜ[ g ] tv v2 : TTop →
    Γ v⊢ₜ[ g ] applyE e v1 v2 : TSing (pv v2).
  Proof.
    move => /= He Hv1 Hv2.
    have Hp: Γ v⊢ₜ[ g0 s0 ⊤ ] tv (packTV 0 s0) : typeEq "A" ⊤.
      by apply: packTV_typed'; [| |lia].
    have Hsub : Γ v⊢ₜ[ g0 s0 ⊤ ] ⊤, 0 <: pv (packTV 0 s0) @; "A", 0
      by eapply iSub_Sel'; tcrush.
    apply (iT_All_Ex (T1 := pv (packTV 0 s0) @; "A") (T2 := TSing p0)); first last.
    by eapply iT_Sub_nocoerce, Hsub.
    eapply iT_All_E; first last.
    by eapply iT_Sub_nocoerce, Hsub.
    apply (iT_All_Ex (v2 := packTV 0 s0) He).
    eapply iT_Sub_nocoerce; [ apply Hp | tcrush ].
  Qed.

  Example foosem e v1 v2:
    let g := g0 s0 ⊤ in
    [] v⊢ₜ[ g ] e : iftFalse →
    [] v⊢ₜ[ g ] tv v1 : TTop →
    [] v⊢ₜ[ g ] tv v2 : TTop →
    s0 ↝n[ 0 ] V⟦ ⊤%ty ⟧ -∗
    [] ⊨ applyE e v1 v2 : TSing (pv v2).
  Proof.
    intros g; subst g.
    iIntros (He Hv1 Hv2) "#Hs".
    iApply fundamental_typed; last by iApply (wellMappedφ_g0 with "Hs").
    exact: foosyn.
  Qed.
(* lett (hclose (htv hloopDefV @: "loop")) *)
  Example barsyn e v1 Γ T :
    is_unstamped_ty' (S (length Γ)) T →
    T :: Γ v⊢ₜ[ g0 s0 ⊤ ] e : Example.iftFalse →
    T :: Γ v⊢ₜ[ g0 s0 ⊤ ] tv v1 : ⊤ →
    T :: Γ v⊢ₜ[ g0 s0 ⊤ ] applyE e v1 x0 : TSing (pv x0).
  Proof.
    intros; apply foosyn => //.
    eapply iT_Var_Sub; [ done | tcrush]. cbn.
    eapply unstamped_stamped_type.
    by rewrite hsubst_id.
  Qed.

  (* Example foo Γ e v1 v2:
    s0 ↝ ⟦ ⊤%ty ⟧ -∗
    [] ⊨ e : iftFalse -∗
    WP applyE e v1 v2 {{v, ⌜ v = v2 ⌝}}.
  Proof.
    rewrite /iftFalse.
    iIntros "#Hs #H". iSpecialize ("H" $! ids with "[#//]").
    rewrite hsubst_id.
    iApply (wp_bind (fill [(AppLCtx _)])).
    iApply (wp_bind (fill [(AppLCtx _)])).
    smart_wp_bind (AppLCtx _) v "{H} #Hr" "H".
    iDestruct "Hr" as (t ->) "#Hr".
    iApply (wp_bind (fill [(AppRCtx _)])).
    iPoseProof (packTV_semTyped [] s0 ⊤ with "Hs") as "#Hp"; first done.
    rewrite -wp_value'.
    rewrite -wp_pure_step_later //=.
    iSpecialize ("Hp" $! ids with "[#//]").
    rewrite wp_value_inv'.
    iSpecialize ("Hr" $! (packTV 0 s0) with "Hp").
    iNext.
    iApply (wp_wand with "Hr"); iIntros "/=" (v).
    iDestruct 1 as (t1 ->) "#H1".
    iSpecialize ("H1" $! v1).

    smart_wp_bind (AppRCtx _) v "#Hr2" "Hr".
    iApply (wp_bind (fill [(AppLCtx _)])).
    smart_wp_bind (AppRCtx _) v "#Hr" "H". *)
End Example.

Section Sec.
  Context `{HdlangG: dlangG Σ}.

  (* Subsumed by transitivity. *)
  (* Global Instance: Proper (flip ctx_sub ==> ctx_sub ==> impl) ctx_sub.
  Proof. rewrite /flip => x y H x0 y0 H1 H2. by rewrite -H1 H. (* trans x => //. by trans x0. *) Qed.
  Global Instance: Proper (ctx_sub ==> flip ctx_sub ==> flip impl) ctx_sub.
  Proof. rewrite /flip => x y H x0 y0 H1 H2. by rewrite H -H1. Qed. *)

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

  Lemma T_All_I1 {Γ} T1 T2 e:
    TLater (shift T1) :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  (* Proof. rewrite -T_All_I. f_equiv. iIntros (ρ) "[$ $]". Qed. *)
  Proof.
    rewrite -(T_All_I_Strong (Γ' := Γ)) //; ietp_weaken_ctx.
    (* by rewrite -(unTLater_ctx_sub (TLater _ :: _)). *)
    (* apply ietp_weaken_ctx_syn. *)
    (* exact: (unTLater_ctx_sub_syn (TLater _ :: _)). *)
  Qed.

  Lemma T_All_I2 {Γ} T1 T2 e:
    TLater (shift T1) :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof. rewrite -T_All_I. ietp_weaken_ctx. Qed.

  (* Lemma T_All_I4 {Γ} T1 T2 e:
    TLater (shift T1) :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    rewrite -T_All_I_Strong -(unTLater_ctx_sub (TLater _ :: _)).
    by rewrite fmap_cons cancel.
  Qed. *)

  Lemma All_Later_Sub_Distr0 Γ T U `{SwapPropI Σ}:
    Γ ⊨ TAll (TLater T) U, 0 <: TLater (TAll T U), 0.
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

  (* It doesn't work, modulo maybe except-n. *)
  Lemma T_Path'' Γ T p i :
    Γ ⊨p p : T, i -∗
    Γ ⊨ path2tm p : iterate TLater i T.
  Proof.
    iIntros "#Hep !>" (ρ) "#Hg /= !>"; rewrite path2tm_subst.
    iApply wp_wand. iPoseProof (path_wp_to_wp with "(Hep Hg)") as "?".
    (* We're stuck here. *)
  Abort.

  Lemma wp_later_swap t Φ: WP t {{ v, ▷ Φ v }} ⊢ ▷ WP t {{ v, Φ v }}.
  Proof.
    iLöb as "IH" forall (t Φ).
    iEval (rewrite !wp_unfold /wp_pre /=).
    case: (to_val t) => [v|]. by eauto.
    iIntros "H" (σ1 κ κs n _); iDestruct ("H" $! σ1 κ κs n with "[#//]") as "[$ H]".
    iIntros (e2 σ2 efs Hstep); iDestruct ("H" $! e2 σ2 efs Hstep) as "[$ [H $]]".
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
    Γ ⊨ TAll (TLater T) (TLater U), i <: TLater (TAll T U), i.
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
    Γ ⊨ TVMem l (TLater T), i <: TLater (TVMem l T), i.
  Proof.
    iIntros "!>" (ρ v) "_ /= #HvT". iNext i.
    iDestruct "HvT" as (d Hlook) "#HvT".
    iExists (d); (iSplit; try iSplit) => //.
    iDestruct "HvT" as (pmem ->) "HvT".
    rewrite path_wp_later_swap.
    iExists (pmem); by iSplit.
  Qed.

  (** Unlike the other lemmas, this appears to fail, and that makes sense.
  It says that if you have *now* a type member between ▷ L and ▷ U, then you
  also have *later* a type member between L and U; I don't see a reason for
  that to be true.
  *)
  Lemma Typ_Later_Sub_Distr `{SwapPropI Σ} Γ L U i l:
    Γ ⊨ TTMem l (TLater L) (TLater U), i <: TLater (TTMem l L U), i.
  Proof.
    rewrite /istpi/=.
    iIntros (ρ v) "!> #Hg #Hv !>"; iDestruct "Hv" as (d Hl ψ) "H".
    iExists d; iFrame (Hl); iExists ψ. iDestruct "H" as "[$ #[H1 H2]] {H}".
    rewrite /= !later_intuitionistically; iModIntro (□ _)%I; iSplit; iIntros (w).
    rewrite -mlater_impl; iIntros "H"; iApply "H1"; iApply "H".
    rewrite -mlater_impl; iIntros "H"; iApply "H2".
    Fail iApply "H".
  Abort.

  (* This would be surprising without ◇, and fails even with it. *)
  (* Lemma wp_later_swap2 t Φ: ▷ WP t {{ v, Φ v }} ⊢ ◇ WP t {{ v, ▷ Φ v }}. *)

  Lemma sSub_Mono Γ T i :
    Γ s⊨ T, i <: T, S i.
  Proof. by iIntros "!> **". Qed.

  (** Rename. *)
  Lemma iterate_Sub_Mono Γ T i j:
    Γ ⊨ T, i <: T, j + i.
  Proof.
    iInduction j as [] "IHj".
    - iApply Sub_Refl.
    - iApply (Sub_Trans with "IHj").
      iApply sSub_Mono.
  Qed.

  Lemma iterate_Sub_Later Γ T i j:
    Γ ⊨ T, j + i <: iterate TLater j T, i.
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
    Γ ⊨ iterate TLater j T, i <: T, i + j.
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

  (** Core definitions for singleton types. ⟦ w.type ⟧ ρ v *)
  Definition sem_singleton w ρ v : iProp Σ := ⌜ w.[ρ] = v ⌝.
  Arguments sem_singleton /.

  (* Core typing lemmas, sketches. TODO: make the above into a type, and add all
     the plumbing. *)
  Lemma self_sem_singleton ρ v: sem_singleton v ρ v.[ρ].
  Proof. by iIntros "!%". Qed.

  Lemma other_sem_singleton ρ w v v':
    (sem_singleton w ρ v.[ρ] →
    sem_singleton w ρ v' ↔ sem_singleton v ρ v')%I.
  Proof. iIntros (Hv) "/="; iSplit; iIntros (Hv1) "!%"; by simplify_eq. Qed.

  Lemma tskip_self_sem_singleton ρ v:
    WP (tskip (tv v.[ρ])) {{ w, sem_singleton v ρ w }}%I.
  Proof. rewrite -wp_pure_step_later // -wp_value /=. by iIntros "!%". Qed.

  Lemma tskip_other_sem_singleton ρ w v v':
    sem_singleton w ρ v -∗
    WP (tskip (tv v)) {{ sem_singleton w ρ }}.
  Proof. iIntros (H); rewrite -wp_pure_step_later // -wp_value' //=. Qed.

  (* v : p.type *)
  (* Definition sem_psingleton p ρ v : iProp Σ := path_wp p.|[ρ] (λ w, ⌜ w = v ⌝ )%I.
  Global Arguments sem_psingleton /.
  Global Instance: Persistent (sem_psingleton p ρ v) := _.

  Lemma psingletons_equiv w ρ v: sem_singleton w ρ v ⊣⊢ sem_psingleton (pv w) ρ v.
  Proof. done. Qed.

  Lemma self_sem_psingleton p ρ v :
    path_wp p.|[ρ] (λ w, ⌜ v = w ⌝) -∗ path_wp p.|[ρ] (sem_psingleton p ρ).
  Proof.
    iIntros (Heq) "/=".
    iEval rewrite path_wp_eq. iExists v; iFrame (Heq). iIntros "!%".
  Qed.

  Lemma T_self_sem_psingleton Γ p T i :
    Γ ⊨p p : T , i -∗
    (* Γ ⊨p p : sem_psingleton p , i *)
    □∀ ρ, G⟦Γ⟧ ρ →
      ▷^i path_wp (p.|[ρ])
      (λ v, sem_psingleton p ρ v).
  Proof.
    iIntros "#Hp !>" (vs) "#Hg".
    iSpecialize ("Hp" with "Hg"); iNext i.
    rewrite !path_wp_eq.
    iDestruct "Hp" as (v) "(Heq & _)". by iExists v; iFrame "Heq".
  Qed. *)

  (* Lemma nsteps_ind_r_weak `(R : relation A) (P : nat → A → A → Prop)
    (Prefl : ∀ x, P 0 x x) (Pstep : ∀ x y z n, relations.nsteps R n x y → R y z → P n x y → P (S n) x z) :
    ∀ x z n, relations.nsteps R n x z → P n x z.
  Proof.
    cut (∀ y z m n, relations.nsteps R n y z → ∀ x, relations.nsteps R m x y → P m x y → P (m + n) x z); first last.
    (* { eauto using relations.nsteps_0. } *)
    Search _ (_ + S _ = S (_ + _)).
    induction 1; rewrite /= ?Nat.add_0_r; eauto using nsteps_trans, nsteps_r.
    intros. eapply Pstep. [apply H1|..]. nsteps_r.
  Abort. *)


  (* Lemma self_sem_psingleton p:
    nclosed p 0 → path_wp p (sem_psingleton p []).
  Proof.
    elim: p => [v|p IHp l] /=; asimpl.
    by iIntros (Hcl%fv_pv_inv) "!> !%".

    iIntros (Hcl%fv_pself_inv).

  Lemma path_wp_exec2 {p v m} :
    PureExec True m (path2tm p) (tv v) →
    path_wp p (λ w, ⌜ w = v ⌝ : iProp Σ)%I.
  Lemma self_sem_psingleton3 p i v:
    PureExec True i (path2tm p) (tv v) →
    path_wp p (sem_psingleton p ids).
  Proof.
    iIntros (Hexec) "/=".
    rewrite hsubst_id !path_wp_eq. iExists v.
    iDestruct (path_wp_exec2 Hexec) as "#$".
  Qed. *)
End Sec.
