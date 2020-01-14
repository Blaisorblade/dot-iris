From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language ectx_language ectxi_language.
From iris.proofmode Require Import tactics.
From D Require Import swap_later_impl.
From D.Dot.syn Require Import synLemmas rules path_repl.
From D.Dot.lr Require Import unary_lr
  lr_lemmas lr_lemmasTSel lr_lemmasNoBinding lr_lemmasDefs path_repl.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (p : path)
         (Γ : ctx).

Definition path_includes p ρ ds :=
  path_wp_pure p.|[ρ] (λ w, ∃ ds', w = vobj ds' ∧ ds.|[ρ] `sublist_of` ds'.|[w/]).

Lemma path_includes_self ds ρ : path_includes (pv (ids 0)) (vobj ds.|[up ρ] .: ρ) ds.
Proof. eexists; split; by [| rewrite up_sub_compose]. Qed.

Lemma path_includes_split p ρ l d ds :
  path_includes p ρ ((l, d) :: ds) →
  path_includes p ρ [(l, d)] ∧
  path_includes p ρ ds.
Proof.
  rewrite /path_includes !path_wp_pure_eq; cbn.
  intros (v & Hpw & ds' & -> & (k1 & k2 & Hpid' & Hpids)%sublist_cons_l).
  split; exists (vobj ds'); split => //; exists ds'; split => //; rewrite Hpid'.
  by apply sublist_inserts_l, sublist_skip, sublist_nil_l.
  by apply sublist_inserts_l, sublist_cons, Hpids.
Qed.

Section NestIdentity.
  Context `{HdlangG: dlangG Σ}.

  Definition idtp p Γ T l d : iProp Σ :=
    □∀ ρ, ⌜path_includes p ρ [(l, d)] ⌝ → ⟦Γ⟧* ρ → def_interp T l ρ d.|[ρ].
  Global Arguments idtp /.

  Definition idstp p Γ T ds : iProp Σ :=
    □∀ ρ, ⌜path_includes p ρ ds ⌝ → ⟦Γ⟧* ρ → defs_interp T ρ ds.|[ρ].
  Global Arguments idstp /.

  Local Notation IntoPersistent' P := (IntoPersistent false P P).
  Global Instance idtp_persistent p Γ T l d: IntoPersistent' (idtp p Γ T l d) | 0 := _.
  Global Instance idstp_persistent p Γ T ds: IntoPersistent' (idstp p Γ T ds) | 0 := _.

  (** Single-definition typing *)
  Notation "Γ ⊨[ p ] {  l := d  } : T" := (idtp p Γ T l d) (at level 74, d, l, T at next level).
  (** Multi-definition typing *)
  Notation "Γ ⊨[ p ]ds ds : T" := (idstp p Γ T ds) (at level 74, ds, T at next level).

  From D.Dot.lr Require Import typeExtractionSem.
  Notation "s ↝[  σ  ] φ" := (leadsto_envD_equiv s σ φ) (at level 20).

  Lemma D_Typ_Abs Γ T L U s σ l p :
    Γ ⊨ TLater T, 0 <: TLater U, 0 -∗
    Γ ⊨ TLater L, 0 <: TLater T, 0 -∗
    s ↝[ σ ] ⟦ T ⟧ -∗
    Γ ⊨[ p ] { l := dtysem σ s } : TTMem l L U.
  Proof.
    iIntros "#HTU #HLT #Hs /= !>" (ρ Hpid) "#Hg".
    iDestruct "Hs" as (φ Hγφ) "Hγ"; iSplit => //=.
    iExists (φ _); iSplit. by iApply (dm_to_type_intro with "Hγ").
    iModIntro; repeat iSplit; iIntros (v) "#HL";
      rewrite later_intuitionistically.
    - iIntros "!>". iApply Hγφ. by iApply "HLT".
    - iApply "HTU" => //. by iApply Hγφ.
  Qed.

  Lemma TVMem_I {Γ} V T v l p:
    TLater V :: Γ ⊨ tv v : T -∗
    Γ |L V ⊨[ p ] { l := dvl v } : TVMem l T.
  Proof.
    iIntros "/= #Hv !>" (ρ Hpid) "[#Hg #Hw]".
    rewrite def_interp_tvmem_eq.
    iApply wp_value_inv'; iApply ("Hv" with "[]"); by iSplit.
  Qed.

  Lemma TVMem_All_I {Γ} V T1 T2 e l p:
    T1.|[ren (+1)] :: V :: Γ ⊨ e : T2 -∗
    Γ |L V ⊨[ p ] { l := dvl (vabs e) } : TVMem l (TAll T1 T2).
  Proof.
    iIntros "HeT"; iApply TVMem_I.
    (* Compared to [T_Forall_I], we must strip the later from [TLater V]. *)
    iApply T_Forall_I_Strong;
      iApply (ietp_weaken_ctx with "HeT") => ρ.
    by rewrite /= ctx_sub_unTLater.
  Qed.

  Context Γ.

  Lemma TVMem_Sub V T1 T2 v l p:
    Γ |L V ⊨ T1, 0 <: T2, 0 -∗
    Γ |L V ⊨[ p ] { l := dvl v } : TVMem l T1 -∗
    Γ |L V ⊨[ p ] { l := dvl v } : TVMem l T2.
  Proof.
    iIntros "/= #Hsub #Hv !>" (ρ Hpid) "#Hg"; iApply def_interp_tvmem_eq.
    iApply ("Hsub" with "Hg").
    iApply def_interp_tvmem_eq. by iApply "Hv".
  Qed.

  Lemma DNil_I p : Γ ⊨[ p ]ds [] : TTop.
  Proof. by iIntros "!> **". Qed.

  Lemma DCons_I p d ds l T1 T2:
    dms_hasnt ds l →
    Γ ⊨[ p ] { l := d } : T1 -∗ Γ ⊨[ p ]ds ds : T2 -∗
    Γ ⊨[ p ]ds (l, d) :: ds : TAnd T1 T2.
  Proof.
    iIntros (Hlds) "#HT1 #HT2 !>". iIntros (ρ [Hpid Hpids]%path_includes_split) "#Hg /=".
    iSpecialize ("HT1" $! _  Hpid with "Hg"). iPoseProof "HT1" as (Hl) "_".
    iSpecialize ("HT2" $! _  Hpids with "Hg").
    iSplit.
    - destruct T1; simplify_eq; iApply (def2defs_head with "HT1").
    - iApply (defs_interp_mono with "HT2"); by [apply dms_hasnt_map_mono | eapply nclosed_sub_app].
  Qed.

  Lemma T_New_I T ds:
     Γ |L T ⊨[ pv (ids 0) ]ds ds : T -∗
     Γ ⊨ tv (vobj ds) : TMu T.
  Proof.
    iIntros "/= #Hds !>" (ρ) "#Hg /= !>". rewrite -wp_value'.
    iLöb as "IH".
    iApply lift_dsinterp_dms_vl_commute.
    rewrite norm_selfSubst.
    have Hs := path_includes_self ds ρ.
    iApply ("Hds" $! (vobj _ .: ρ) Hs). by iFrame "IH Hg".
  Qed.

End NestIdentity.

(** These typing lemmas can be derived syntactically.
 But I had written semantic proofs first, and they might help. *)
Section AlsoSyntactically.
  Context `{HdlangG: dlangG Σ}.

  (* Also derivable syntactically. *)
  Lemma singleton_Mu_1 {Γ p T i T'} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : TMu T, i -∗
    Γ ⊨ TSing p, i <: T', i.
  Proof. rewrite (TMu_E_p Hrepl). apply singleton_self_sub. Qed.

  Lemma singleton_Mu_2 {Γ p T i T'} (Hrepl : T .Tp[ p /]~ T') :
    Γ ⊨p p : T', i -∗
    Γ ⊨ TSing p, i <: TMu T, i.
  Proof. rewrite (TMu_I_p Hrepl). apply singleton_self_sub. Qed.

  (** Semantic version of derived rule [singleton_Mu_dotty1]. *)
  Lemma singleton_Mu_dotty1 {Γ p i T1 T2 T1' T2'}
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
    iApply (P_Sub' with "Hp Hsub").
  Qed.

End AlsoSyntactically.


From D.Dot Require exampleInfra typingExInfra.
From D.Dot Require fundamental typingStamping.
From D.Dot.examples Require scalaLib.

Section Example.
  Context `{HdlangG: dlangG Σ} `{SwapPropI Σ}.
  Import exampleInfra typingExInfra fundamental typingStamping scalaLib.

  Lemma OrSplit Γ e1 e2 A B C :
    Γ ⊨ e1 : TOr A B -∗
    shift A :: Γ ⊨ e2 : shift C -∗
    shift B :: Γ ⊨ e2 : shift C -∗
    Γ ⊨ lett e1 e2 : C.
  Proof.
    iIntros "He #HA #HB".
    iApply (T_Forall_E with "[] He").
    iApply T_Forall_I.
    iSimpl; iIntros "!>" (ρ) "#[Hg [H|H]] !>";
      [iApply ("HA" with "[]") | iApply ("HB" with "[]")];
      iFrame "Hg H".
  Qed.

  Definition iftFalse := (∀: tparam "A", (∀: p0 @; "A", (∀: p1 @; "A", TSing p0)))%ty.
  Definition s0 := 1%positive.
  Definition g0 s T : stys := <[ s := T ]>∅.

  Import stamp_transfer astStamping.

  Lemma wellMappedφ_g0 s T:
    s ↝ ⟦ T ⟧ -∗
    wellMappedφ (⟦ g0 s T ⟧g).
  Proof.
    iIntros "Hs"; rewrite fmap_insert.
    iApply (wellMappedφ_insert with "[] Hs"); iApply wellMappedφ_empty.
  Qed.

  Definition applyE e v1 v2 := e $: tv (packTV 0 s0) $: tv v1 $: tv v2.

  (* XXX "only empty context" won't be enough :-( *)
  Example foo1 Γ s T (Hcl : nclosed T 0) :
    s ↝ ⟦ T ⟧ -∗
    (* Γ ⊨ tv (packTV (length Γ) s) : typeEq "A" T. *)
    [] ⊨ tv (packTV 0 s) : typeEq "A" T.
  Proof.
    iIntros "#Hs !>" (ρ) "#_ /= !>".
    rewrite -wp_value'.
    iExists (dtysem [] s); iSplit; first eauto.
    iExists (⟦ T ⟧ ids); iSplit; first by iApply (dm_to_type_intro _ _ []).
    iModIntro; iSplit; iIntros (v) "#H !>";
      by rewrite (interp_subst_ids T ρ v) (closed_subst_id _ Hcl).
  Qed.

  (* XXX use more semantic typing. *)
  Example packTV_semTyped Γ s T (Hu: is_unstamped_ty (length Γ) T):
    s ↝ ⟦ T ⟧ -∗
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
    by rewrite -interp_subst_commute ?length_idsσ ?closed_subst_idsρ.
    eauto 10.
    Restart. *)
    iIntros "#Hs".
    (* iAssert (wellMappedφ (⟦ <[ s := T ]>∅ ⟧g)) as "#Hw". *)
    iApply fundamental_typed; last by iApply (wellMappedφ_g0 with "Hs").
    have Hst: is_stamped_ty (length Γ) (<[s:=T]> ∅) T.
    exact: unstamped_stamped_type.
    (* eapply Subs_typed_nocoerce. *)
    eapply packTV_typed'; rewrite //= ?lookup_insert //.
    (* tcrush. *)
  Qed.
    (* Unshelve.
    done.
    apply typing_obj_ident_to_typing.

    rewrite -(iterate_0 tskip (tv _)).
    iApply (T_Sub _ _ ((μ {@ typeEq "A" T.|[ren (+1)] }))); first last.
    iApply Sub_Mu_1; rewrite iterate_0.
    iApply Sub_Trans. iApply
    iApply T_New_I.
  Qed. *)

  Example foo Γ e v1 v2:
    s0 ↝ ⟦ ⊤%ty ⟧ -∗
    [] ⊨ e : iftFalse -∗
    [] ⊨ tv v1 : TTop -∗
    [] ⊨ tv v2 : TTop -∗
    [] ⊨ applyE e v1 v2 : TSing (pv v2).
  Proof.
    rewrite /iftFalse.
    iIntros "#Hs #He #Hv1 #Hv2".
    iAssert ([] ⊨ ⊤, 0 <: pv (packTV 0 s0) @; "A", 0) as "#Hsub". {
      iApply Sub_Trans.
      iApply Sub_Add_Later.
      iApply Sub_Sel_Path.
      iApply P_Val.
      iApply (packTV_semTyped with "Hs"); stcrush.
    }
    iApply (T_Forall_Ex _ _ v2 (pv (packTV 0 s0) @; "A") (TSing p0)); first last.
    iApply (T_Sub _ _ _ _ 0 with "Hv2 Hsub").
    iApply T_Forall_E; first last.
    iApply (T_Sub _ _ _ _ 0 with "Hv1 Hsub").
    Timeout 1 iApply (T_Forall_Ex [] e (packTV 0 s0) with "He").
    iApply (T_Sub _ _ (typeEq "A" ⊤) _ 0).
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
      by eapply LSel_stp'; tcrush.
    apply (Appv_typed _ _ _ v2 (pv (packTV 0 s0) @; "A") (TSing p0)); first last.
    by eapply Subs_typed_nocoerce, Hsub.
    eapply App_typed; first last.
    by eapply Subs_typed_nocoerce, Hsub.
    apply (Appv_typed _ _ e (packTV 0 s0) _ _ He).
    eapply Subs_typed_nocoerce; [ apply Hp | tcrush ].
  Qed.

  Example foosem Γ e v1 v2:
    let g := g0 s0 ⊤ in
    [] v⊢ₜ[ g ] e : iftFalse →
    [] v⊢ₜ[ g ] tv v1 : TTop →
    [] v⊢ₜ[ g ] tv v2 : TTop →
    s0 ↝ ⟦ ⊤%ty ⟧ -∗
    [] ⊨ applyE e v1 v2 : TSing (pv v2).
  Proof.
    intros g; subst g.
    iIntros (He Hv1 Hv2) "#Hs".
    iApply fundamental_typed; last by iApply (wellMappedφ_g0 with "Hs").
    exact: foosyn.
  Qed.
(* lett (hclose (htv hloopDefV @: "loop")) *)
  Example barsyn e v1 Γ T :
    is_unstamped_ty (S (length Γ)) T →
    T :: Γ v⊢ₜ[ g0 s0 ⊤ ] e : Example.iftFalse →
    T :: Γ v⊢ₜ[ g0 s0 ⊤ ] tv v1 : ⊤ →
    T :: Γ v⊢ₜ[ g0 s0 ⊤ ] applyE e v1 x0 : TSing (pv x0).
  Proof.
    intros; apply foosyn => //.
    eapply Var_typed_sub; [ done | tcrush]. cbn.
    apply unstamped_stamped_type.
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

  Lemma T_later_ctx Γ V T e:
    TLater <$> (V :: Γ) ⊨ e : T -∗
    (*─────────────────────────*)
    TLater V :: Γ ⊨ e : T.
  Proof. iApply ietp_weaken_ctx => ρ; cbn. by rewrite (TLater_ctx_sub Γ). Qed.

  (*
    Variant of [PT_Mem_I]: not needed here, and we get an extra later :-|, tho it
    matches [T_Mem_E']. *)
  Lemma T_Mem_I Γ e T l:
    Γ ⊨ tproj e l : T -∗
    (*─────────────────────────*)
    Γ ⊨ e : TVMem l (TLater T).
  Proof.
    iIntros "#HE /= !>" (ρ) "#HG !>".
    iSpecialize ("HE" with "HG").
    rewrite (wp_bind_inv (fill [ProjCtx l])) /= /lang.of_val.
    iApply (wp_wand with "HE"); iIntros "/=" (v) "{HE}HE".
    rewrite wp_unfold /wp_pre/=.
    remember (tproj (tv v) l) as v'.
    iDestruct ("HE" $! () [] [] 0 with "[//]") as (Hs) "HE".
    have {Hs} [w [Hhr Hl]]: ∃ w, head_step v' () [] (tv w) () [] ∧ v @ l ↘ dvl w. {
      have Hhr: head_reducible v' ().
        apply prim_head_reducible, ectxi_language_sub_redexes_are_values;
          by [|move => -[]/= *; simplify_eq/=; eauto].
      destruct Hhr as ([] & e2 & [] & efs & Hhr'); last now inversion Hhr'.
      inversion Hhr'; simplify_eq/=. eauto.
    }
    iDestruct ("HE" with "[%]") as "(_ & ? & _)"; first exact: head_prim_step.
    rewrite wp_value_inv'. eauto.
  Qed.

  Lemma T_Forall_I' {Γ} T1 T2 e:
    TLater T1.|[ren (+1)] :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "HeT"; iApply T_Forall_I;
      iApply (ietp_weaken_ctx with "HeT").
    iIntros (ρ) "[$ $]".
  Qed.

  Lemma TAll_Later_Swap0 Γ T U `{SwapPropI Σ}:
    Γ ⊨ TAll (TLater T) U, 0 <: TLater (TAll T U), 0.
  Proof.
    iIntros "!>" (ρ v) "_ /= #HvTU".
    iDestruct "HvTU" as (t ->) "#HvTU".
    iExists t; iSplit => //. iNext.
    iIntros (w) "!>".
    iIntros "#HwT".
    by iApply ("HvTU" with "[# $HwT]").
  Qed.

  Lemma iptp2ietp' i Γ T p :
    Γ ⊨p p : iterate TLater i T, 0 -∗
    Γ ⊨ iterate tskip i (path2tm p) : T.
  Proof.
    rewrite iptp2ietp.
    iIntros "Hp". iApply (T_Sub with "Hp").
    iIntros "!> **"; by rewrite iterate_TLater_later.
  Qed.

  (* It doesn't work, modulo maybe except-n. *)
  Lemma iptp2ietp'' Γ T p i :
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

  Lemma T_Forall_I'' Γ T1 T2 e :
    TLater T1.|[ren (+1)] :: Γ ⊨ e : TLater T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "/= #HeT !>" (vs) "#HG !>".
    rewrite -wp_value'. iExists _; iSplit; first done.
    iIntros "!>" (v) "#Hv"; rewrite up_sub_compose.
    (* iApply (wp_later_swap _ (⟦ T2 ⟧ (v .: vs))).
    iApply ("HeT" $! (v .: vs) with "[$HG]"). *)
    iSpecialize ("HeT" $! (v .: vs) with "[#$HG]").
    by rewrite (interp_weaken_one T1 _ v).
    by rewrite wp_later_swap; iNext.
    (* by iDestruct (wp_later_swap with "HeT") as "{HeT} HeT"; iNext. *)
  Qed.

  (** Stronger version of TAll_Later_Swap0, needs wp_later_swap, which
      might not extend to stronger WPs?*)
  Lemma TAll_Later_Swap `{SwapPropI Σ} Γ T U i:
    Γ ⊨ TAll (TLater T) (TLater U), i <: TLater (TAll T U), i.
  Proof.
    iIntros "!>" (ρ v) "_ /= #HvTU". iNext i.
    iDestruct "HvTU" as (t ->) "#HvTU".
    iExists t; iSplit => //.
    rewrite -mlater_pers. iModIntro (□ _)%I.
    iIntros (w). iSpecialize ("HvTU" $! w).
    rewrite !later_intuitionistically -(wp_later_swap _ (⟦ _ ⟧ _)).
    rewrite -impl_later later_intuitionistically.
    (* Either: *)
    (* done. *)
    (* Or keep the old but more flexible code: *)
    iIntros "#HwT".
    iApply ("HvTU" with "HwT").
  Qed.

  Lemma TVMem_Later_Swap Γ l T i:
    Γ ⊨ TVMem l (TLater T), i <: TLater (TVMem l T), i.
  Proof.
    iIntros "!>" (ρ v) "_ /= #HvT". iNext i.
    iDestruct "HvT" as (d Hlook) "#HvT".
    iExists (d); (iSplit; try iSplit) => //.
    iDestruct "HvT" as (vmem ->) "HvT".
    iExists (vmem); by iSplit.
  Qed.

  (* This would be surprising without ◇, and fails even with it. *)
  Lemma wp_later_swap2 t Φ: ▷ WP t {{ v, Φ v }} ⊢ ◇ WP t {{ v, ▷ Φ v }}.
  Proof.
    iLöb as "IH" forall (t Φ).
    iEval (rewrite !wp_unfold /wp_pre /=).
    case: (to_val t) => [v|]. eauto.
    iIntros "H" (σ1 κ κs n _); iDestruct ("H" $! σ1 κ κs n with "[#//]") as "[Hr H]".
    iSplit. iApply (timeless with "Hr").
    iIntros (e2 σ2 efs Hstep); iDestruct ("H" $! e2 σ2 efs Hstep) as "[_ [H H2]]".
    iSplit => //. iSplitR "H2"; first last.
    unshelve (iApply (timeless with "H2")); first last.
    2: iSpecialize ("IH" with "H").
  Abort.

  (** Rename. *)
  Lemma iterate_Sub_Mono Γ T i j:
    Γ ⊨ T, i <: T, j + i.
  Proof.
    iInduction j as [] "IHj".
    - iApply Sub_Refl.
    - iApply (Sub_Trans with "IHj").
      iApply Sub_Mono.
  Qed.

  Lemma iterate_Sub_Later Γ T i j:
    Γ ⊨ T, j + i <: iterate TLater j T, i.
  Proof.
      iInduction j as [] "IHj" forall (T).
    - iApply Sub_Refl.
    - iApply Sub_Trans; rewrite ?iterate_Sr /=.
      + iApply Sub_Later.
      + iApply ("IHj" $! (TLater T)).
  Qed.

  Lemma Distr_TLater_And T1 T2 ρ v:
    ⟦ TLater (TAnd T1 T2) ⟧ ρ v ⊣⊢
    ⟦ TAnd (TLater T1) (TLater T2) ⟧ ρ v.
  Proof. iSplit; iIntros "/= [$ $]". Qed.

  Lemma selfIntersect Γ T U i j:
    Γ ⊨ T, i <: U, j + i -∗
    Γ ⊨ T, i <: TAnd U T, j + i .
  Proof.
    iIntros "H"; iApply (Sub_And with "[H//] []").
    iApply iterate_Sub_Mono.
  Qed.

  Lemma selfIntersectLater Γ T U i:
    Γ ⊨ T, i <: TLater U, i -∗
    Γ ⊨ T, i <: TLater (TAnd T U), i .
  Proof.
    iIntros "H"; iSimpl; setoid_rewrite Distr_TLater_And.
    iApply (Sub_And with "[] H").
    iApply (Sub_Trans _ T _ _ (S i)).
    - by iApply Sub_Mono.
    - by iApply Sub_Later.
  Qed.

  Lemma Distr_TLaterN_And T1 T2 j ρ v:
    ⟦ iterate TLater j (TAnd T1 T2) ⟧ ρ v ⊣⊢
    ⟦ TAnd (iterate TLater j T1) (iterate TLater j T2) ⟧ ρ v.
  Proof.
    rewrite /= !iterate_TLater_later /=.
    iSplit; iIntros "/= [??]"; iSplit; by [].
  Qed.

  Lemma sub_rewrite_2 Γ T U1 U2 i:
    (∀ ρ v, ⟦ U1 ⟧ ρ v ⊣⊢ ⟦ U2 ⟧ ρ v) →
    Γ ⊨ T, i <: U1, i ⊣⊢
    Γ ⊨ T, i <: U2, i .
  Proof.
    iIntros (Heq); iSplit; iIntros "/= #H !>" (ρ v) "#Hg #HT";
      [rewrite -Heq //|rewrite Heq //]; by iApply "H".
  Qed.

  Lemma sub_rewrite_1 Γ T1 T2 U i:
    (∀ ρ v, ⟦ T1 ⟧ ρ v ⊣⊢ ⟦ T2 ⟧ ρ v) →
    Γ ⊨ T1, i <: U, i ⊣⊢
    Γ ⊨ T2, i <: U, i .
  Proof.
    iIntros (Heq); iSplit; iIntros "/= #H !>" (ρ v) "#Hg #HT";
      [rewrite -Heq //|rewrite Heq //]; by iApply "H".
  Qed.

  Lemma eq_to_bisub Γ T1 T2 i:
    (∀ ρ v, ⟦ T1 ⟧ ρ v ⊣⊢ ⟦ T2 ⟧ ρ v) → True ⊢
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
    iApply (Sub_And with "[] H").
    iApply (Sub_Trans _ T _ _ (j + i)).
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
      iApply Later_Sub.
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
    □∀ ρ, ⟦Γ⟧* ρ →
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
