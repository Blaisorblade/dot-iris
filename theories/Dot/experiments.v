From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language ectx_language ectxi_language.
From iris.proofmode Require Import tactics.
From D Require Import tactics swap_later_impl proofmode_extra locAsimpl.
From D.Dot Require Import unary_lr unary_lr_binding synLemmas rules
  lr_lemma lr_lemma_nobinding lr_lemmasDefs typeExtractionSem.
Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (p : path)
         (Γ : ctx) (ρ : vls).

Implicit Types (Σ : gFunctors).

Require D.olty.

Module SemTypes.
Import olty.
Include OLty syn syn.

Section SemTypes.
  Context `{HdotG: dlangG Σ}.
  Implicit Types (φ: olty Σ).
  Definition ietp Γ φ e : iProp Σ := (⌜ nclosed e (length Γ) ⌝ ∗
    □∀ ρ, ⟦Γ⟧* ρ → interp_expr φ ρ (e.|[to_subst ρ]))%I.
  Global Arguments ietp /.
  Definition step_indexed_ietp Γ φ e i: iProp Σ :=
    (⌜ nclosed e (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ →
      interp_expr (λ ρ v, ▷^i φ ρ v) ρ (e.|[to_subst ρ]))%I.
  Global Arguments step_indexed_ietp /.

  Definition step_indexed_ivstp Γ φ1 φ2 i j: iProp Σ :=
    (□∀ ρ v, ⌜ nclosed_vl v 0 ⌝ → ⟦Γ⟧*ρ → (▷^i φ1 ρ v) → ▷^j φ2 ρ v)%I.
  Global Arguments step_indexed_ivstp /.
  Notation "Γ ⊨ e : φ" := (ietp Γ φ e) (at level 74, e, φ at next level).
  Notation "Γ ⊨ e : T , i" := (step_indexed_ietp Γ T e i) (at level 74, e, T at next level).
  Notation "Γ ⊨ [ φ1 , i ]  <: [ φ2 , j ]" := (step_indexed_ivstp Γ φ1 φ2 i j) (at level 74, φ1, φ2 at next level): bi_scope.


  (* Global Arguments sem_sel /. *)

  Lemma iterate_TLater_later i (φ : olty Σ) ρ v:
    nclosed_vl v 0 →
    (iterate interp_later i φ) ρ v ≡ (▷^i φ ρ v)%I.
  Proof.
    elim: i => [|i IHi] // => Hcl. rewrite iterate_S /= IHi //.
    iSplit; by [iIntros "#[_ $]" | iIntros "$"].
  Qed.
  Program Definition oLater φ := Olty (interp_later φ) _.
  Next Obligation. rewrite /vclosed /interp_later. by iIntros "* [$_]". Qed.

  Program Definition oInterp T := Olty ⟦ T ⟧ _.
  Next Obligation. rewrite /vclosed=>*. by rewrite interp_v_closed. Qed.

  Definition oTTMem l L U := oInterp (TTMem l L U).
  Definition oTLater L := oInterp (TLater L).
  Definition oTSel p l := oInterp (TSel p l).

  Lemma Sub_Sel Γ L U va l i:
    Γ ⊨ tv va : oTTMem l L U, i -∗
    Γ ⊨ [oTLater L, i] <: [oTSel (pv va) l, i].
  Proof.
    iIntros "/= #[% #Hva] !>" (ρ v Hclv) "#Hg #[_ HvL]". iFrame (Hclv).
    iDestruct (interp_env_props with "Hg") as %[Hclρ Hlen]. rewrite <- Hlen in *.
    iSpecialize ("Hva" with "Hg"); rewrite wp_value_inv'.
    iNext.

    iDestruct "Hva" as (Hclvas' d Hl φ) "#[Hlφ [#HLφ #HφU]]".
    iSpecialize ("HLφ" $! _ Hclv with "HvL").
    iExists φ, d; by repeat iSplit.
  Qed.

  Lemma Sel_Sub Γ L U va l i:
    Γ ⊨ tv va : oTTMem l L U, i -∗
    Γ ⊨ [oTSel (pv va) l, i] <: [oTLater U, i].
  Proof.
    iIntros "/= #[% #Hva] !>" (ρ v Hclv) "#Hg [$ #Hφ]". move: H => Hclva.
    iDestruct (interp_env_props with "Hg") as %[Hclρ Hlen]. rewrite <- Hlen in *.
    iSpecialize ("Hva" with "Hg"); rewrite wp_value_inv'.
    iNext.
    iDestruct "Hva" as (Hclvas d Hl φ) "#[Hlφ [#HLφ #HφU]]".
    iDestruct "Hφ" as (φ1 d1 Hva) "[Hγ #HΦ1v]".
    objLookupDet; subst. iDestruct (stored_pred_agree d _ _ v with "Hlφ Hγ") as "#Hag".
    iApply "HφU" => //. iNext; repeat iModIntro. by iRewrite "Hag".
  Qed.

  (* Alternative (and failed) definition. *)
  Program Definition sem_sel p (l: label) :=
    Olty (λ ρ v, (⌜ nclosed_vl v 0 ⌝ ∧ path_wp p.|[to_subst ρ]
      (λ vp, ∃ ϕ d, ⌜vp @ l ↘ d⌝ ∧ d ↗ ϕ ∧ □ ϕ v))%I) _.
  Next Obligation. rewrite /vclosed=>*. by iIntros "[$_]". Qed.

  Lemma Sub_Sel2 Γ L U va l i:
    Γ ⊨ tv va : oTTMem l L U, i -∗
    Γ ⊨ [oTLater L, i] <: [oLater (sem_sel (pv va) l), i].
  Proof.
    iIntros "/= #[% #Hva] !>" (ρ v Hclv) "#Hg #[_ HvL]". move: H => Hclva. iFrame (Hclv).
    iDestruct (interp_env_props with "Hg") as %[Hclρ Hlen]. rewrite <- Hlen in *.
    iSpecialize ("Hva" with "Hg"); rewrite wp_value_inv'.
    iNext.

    iDestruct "Hva" as (Hclvas' d Hl φ) "#[Hlφ [#HLφ ?]]".
    iSpecialize ("HLφ" $! _ Hclv with "HvL").
    iExists φ, d; by repeat iSplit.
  Qed.

  Lemma Sel_Sub2_Failed Γ L U va l i:
    Γ ⊨ tv va : oTTMem l L U, i -∗
    Γ ⊨ [oLater ((sem_sel (pv va) l)), i] <: [oTLater U, i].
  Proof.
    iIntros "/= #[% #Hva] !>" (ρ v Hclv) "#Hg #[$ #[_ Hφ]]".
    iDestruct (interp_env_props with "Hg") as %[Hclρ Hlen]. rewrite <- Hlen in *.
    iSpecialize ("Hva" with "Hg"); rewrite wp_value_inv'.
    iNext.
    iDestruct "Hva" as (Hclvas d Hl φ) "#[Hlφ [_ #HφU]]".
    iApply "HφU" => //.
    iDestruct "Hφ" as (φ1 d1) "[>% [Hγ #HΦ1v]]".
    (* iSpecialize ("HLφ" $! v Hclv); iSpecialize ("HφU" $! v Hclv). *)
    (* rewrite /sem_sel /olty_car. *)
    objLookupDet; subst. iNext. iDestruct (stored_pred_agree d _ _ v with "Hlφ Hγ") as "#Hag".
    repeat iModIntro. Fail by iRewrite "Hag".
  Abort.

End SemTypes.
End SemTypes.

Module example.
Section ex.
  Context `{HdlangG: dlangG Σ}.

  Definition even v := ∃ n, v = vnat (2 * n).
  Definition ieven: envD Σ := λ ρ v, (⌜ even v ⌝) %I.
  Instance evenP ρ v: Persistent (ieven ρ v) := _.
  Lemma even_nat ρ v : ieven ρ v ⊢ interp_nat ρ v.
  Proof. iIntros ([]) "!% /=". eauto. Qed.

  Context (s: stamp).

  Definition Hs := (s ↝ ieven)%I.
  (** Under Iris assumption [Hs], [v.A] points to [ieven].
      We assume [Hs] throughout the rest of the section. *)
  Definition v := vobj [("A", dtysem [] s); ("n", dvl (vnat 2))].

  (** Yes, v has a valid type member. *)
  Lemma vHasA0: Hs -∗ ⟦ TTMem "A" TBot TNat ⟧ [] v.
  Proof.
    iIntros "#Hs". repeat (repeat iExists _; repeat iSplit; try done).
    iModIntro; repeat iSplit;
    iIntros (v Hcl); rewrite -?even_nat /=; iIntros ">#% //".
  Qed.

  (* Generic useful lemmas — not needed for fundamental theorem,
     but very useful for examples. *)
  Lemma ietp_value T v: nclosed_vl v 0 → ⟦ T ⟧ [] v -∗ [] ⊨ tv v : T.
  Proof.
    iIntros (?) "#H /="; iSplit; first by auto using fv_tv.
    iIntros "!>" (?->).
    rewrite -wp_value' to_subst_nil subst_id. iApply "H".
  Qed.

  Lemma ietp_value_inv T v: [] ⊨ tv v : T -∗ ⟦ T ⟧ [] v.
  Proof.
    iIntros "/= [% H]".
    iDestruct ("H" $! [] with "[//]") as "H".
    by rewrite wp_value_inv' subst_id.
  Qed.

  Lemma vHasA0': Hs -∗ [] ⊨ tv v : TTMem "A" TBot TNat.
  Proof.
    rewrite -ietp_value; by [iApply vHasA0|].
  Qed.

  (* This works. Crucially, we use TMu_I to introduce the object type.
     This way, we can inline the object in the type selection.
     This cannot be done using T_New_I directly.
     However, this is closer to how typechecking in Scala
     actually works.
   *)
  Lemma vHasA1: Hs -∗
    ⟦ TMu (TAnd
          (TTMem "A" TBot TNat)
          (TAnd (TVMem "n" (TSel (pv (ids 0)) "A")) TTop)) ⟧ [] v.
  Proof.
    rewrite -ietp_value_inv -(TMu_I [] _ v).
    iIntros "#Hs".
    iApply TAnd_I; first by [iApply vHasA0'].
    iApply TAnd_I; first last.
    - iApply (T_Sub _ _ _ _ 0); last by iApply Sub_Top.
      by iApply vHasA0'.
    - rewrite -ietp_value /=; last done; iSplit => //.
      do 2 (repeat iExists _; [repeat iSplit]) => //=.
      iNext.
      iExists _, _; repeat iSplit =>//;
      repeat iExists _; [repeat iSplit..] => //=.
      by iExists 1.
      (* by instantiate (1 := 1). *)
  Qed.

  (*
    A different approach would be to type the object using T_New_I
    with an object type [U] with member [TTMem "A" ieven ieven].
    We could then upcast the object. But type U is not syntactic,
    so we can't express this yet using the existing typing
    lemmas.
    And if we use T_New_I on the final type, then [this.A]
    is overly abstract when we try proving that [this.n : this.A];
    see concretely below.
  *)
  Lemma vHasA1': Hs -∗
    ⟦ TMu (TAnd
          (TTMem "A" TBot TNat)
          (TAnd (TVMem "n" (TSel (pv (ids 0)) "A")) TTop)) ⟧ [] v.
  Proof.
    iIntros "#Hs".
    iDestruct (T_New_I [] _ with "[]") as "[% #H]"; first last.
    iSpecialize ("H" $! [] with "[#//]").
    rewrite to_subst_nil hsubst_id /interp_expr wp_value_inv'.
    iApply "H".
    iApply DCons_I => //.
    - (* Can't finish with D_Typ, this is only for syntactic types: *)

      (* iApply D_Typ => //.
      admit. admit. cbn. iSplit => //. iExists _; iSplit => //. *)
      iSplit => //=; iModIntro.
      iIntros ([|v ρ]) "/= #H". done.
      iDestruct "H" as "[-> [% _]]".
      repeat (repeat iExists _; repeat iSplit; try done).
      iModIntro; repeat iSplit;
      iIntros (w Hcl); rewrite -?even_nat /=.
      by iIntros ">?".
      rewrite even_nat.
      by iIntros ">?".
    - iApply DCons_I => //; last by iApply DNil_I.
      iApply TVMem_I.
      iSplit => //=.
      iIntros "!>" ([|v ρ]) "/= #H". done.
      iDestruct "H" as "[-> [[% HA] [[% HB] _]]]".
      rewrite to_subst_cons to_subst_nil /=.
      rewrite -wp_value'; iSplit => //.
      iDestruct "HA" as (dA HlA φ) "[Hlφ HA]".
      iDestruct "HB" as (dB HlB w) "HB".
      iExists φ, dA; repeat iSplit => //.
      (* This will fail, since we don't know what v is and what
      "A" points to. *)
  Abort.
End ex.
End example.

Section Sec.
  Context `{HdlangG: dlangG Σ}.

  Lemma TAll_Later_Swap0 Γ T U `{SwapProp (iPropSI Σ)}:
    Γ ⊨ [TAll (TLater T) U, 0] <: [TLater (TAll T U), 0].
  Proof.
    iIntros "!>" (ρ v Hclv) "_ /= #[_ #HvTU]". iFrame (Hclv).
    iDestruct "HvTU" as (t ->) "#HvTU".
    iExists t; iSplit => //. iNext.
    iIntros (w) "!>".
    rewrite -mlater_impl.
    iIntros "#HwT".
    iApply (strip_pure_laterN_impl 1 (nclosed_vl w 0)); first last.
      by iApply interp_v_closed.
    iIntros (Hclw).
    by iApply ("HvTU" with "[# $HwT]").
  Qed.

  Lemma wp_later_swap t Φ: WP t {{ v, ▷ Φ v }} ⊢ ▷ WP t {{ v, Φ v }}.
  Proof.
    iLöb as "IH" forall (t Φ).
    iEval (rewrite !wp_unfold /wp_pre /=).
    case: (to_val t) => [v|]. eauto.
    iIntros "H" (σ1 κ κs n _); iDestruct ("H" $! σ1 κ κs n with "[#//]") as "[$ H]".
    iIntros (e2 σ2 efs Hstep); iDestruct ("H" $! e2 σ2 efs Hstep) as "[$ [H $]]".
    iApply ("IH" with "H").
  Qed.

  (** Stronger version of TAll_Later_Swap0, needs wp_later_swap, which
      might not extend to stronger WPs?*)
  Lemma TAll_Later_Swap `{SwapProp (iPropSI Σ)} Γ T U i:
    Γ ⊨ [TAll (TLater T) (TLater U), i] <: [TLater (TAll T U), i].
  Proof.
    iIntros "!>" (ρ v Hclv) "_ /= [_ #HvTU]". iFrame (Hclv). iNext i.
    iDestruct "HvTU" as (t ->) "#HvTU".
    iExists t; iSplit => //.
    iNext.
    iIntros (w); rewrite -mlater_impl; iIntros "!> #HwT".
    iApply (strip_pure_laterN_impl 1 (nclosed_vl w 0)); first last.
      by iApply interp_v_closed.
    iIntros (Hclw).
    rewrite -(wp_later_swap _ (⟦ _ ⟧ _)).
    iApply (wp_wand with "(HvTU [# $HwT //])").
    by iIntros (v) "[_ $]".
  Qed.

  Lemma TVMem_Later_Swap Γ l T i:
    Γ ⊨ [TVMem l (TLater T), i] <: [TLater (TVMem l T), i].
  Proof.
    iIntros "!>" (ρ v Hclv) "_ /= #[_ #HvT]". iFrame (Hclv). iNext i.
    iDestruct "HvT" as (d Hlook) "#HvT".
    iExists (d); (iSplit; try iSplitL) => //.
    iDestruct "HvT" as (vmem ->) "[_ HvT]".
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
    iApply (timeless with "H2"). admit.
    iSpecialize ("IH" with "H").
  Abort.

  (** Rename. *)
  Lemma iterate_Sub_Mono Γ T i j:
    Γ ⊨ [ T, i ] <: [T, j + i].
  Proof.
    iInduction j as [] "IHj".
    - iApply Sub_Refl.
    - iApply (Sub_Trans with "IHj").
      iApply Sub_Mono.
  Qed.

  Lemma iterate_Sub_Later Γ T i j:
    Γ ⊨ [T, j + i] <: [iterate TLater j T, i].
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
  Proof.
    iSplit.
    iIntros "/= [$ [??]]"; eauto.
    iIntros "/= [[$?] [_?]]"; eauto.
  Qed.

  Lemma selfIntersect Γ T U i j:
    Γ ⊨ [ T, i ] <: [ U, j + i ] -∗
    Γ ⊨ [ T, i ] <: [ TAnd U T, j + i ].
  Proof.
    iIntros "H"; iApply (Sub_And with "[H//] []").
    iApply iterate_Sub_Mono.
  Qed.

  Lemma selfIntersectLater Γ T U i:
    Γ ⊨ [ T, i ] <: [ TLater U, i ] -∗
    Γ ⊨ [ T, i ] <: [ TLater (TAnd T U), i ].
  Proof.
    iIntros "H"; iSimpl; setoid_rewrite Distr_TLater_And.
    iApply (Sub_And with "[] H").
    iApply (Sub_Trans _ _ T _ _ (S i)).
    - by iApply Sub_Mono.
    - by iApply Sub_Later.
  Qed.

  Lemma Distr_TLaterN_And T1 T2 j ρ v:
    nclosed_vl v 0 →
    ⟦ iterate TLater j (TAnd T1 T2) ⟧ ρ v ⊣⊢
    ⟦ TAnd (iterate TLater j T1) (iterate TLater j T2) ⟧ ρ v.
  Proof.
    intro Hclv.
    rewrite /= !iterate_TLater_later //=.
    iSplit; iIntros "/= [??]"; iSplit; by [].
  Qed.

  Lemma sub_rewrite_2 Γ T U1 U2 i:
    (∀ ρ v, nclosed_vl v 0 → ⟦ U1 ⟧ ρ v ⊣⊢ ⟦ U2 ⟧ ρ v) →
    Γ ⊨ [ T, i ] <: [ U1, i ] ⊣⊢
    Γ ⊨ [ T, i ] <: [ U2, i ].
  Proof.
    iIntros (Heq); iSplit; iIntros "/= #H !>" (ρ v Hcl) "#Hg #HT";
      [rewrite -Heq //|rewrite Heq //]; by iApply "H".
  Qed.

  Lemma sub_rewrite_1 Γ T1 T2 U i:
    (∀ ρ v, nclosed_vl v 0 → ⟦ T1 ⟧ ρ v ⊣⊢ ⟦ T2 ⟧ ρ v) →
    Γ ⊨ [ T1, i ] <: [ U, i ] ⊣⊢
    Γ ⊨ [ T2, i ] <: [ U, i ].
  Proof.
    iIntros (Heq); iSplit; iIntros "/= #H !>" (ρ v Hcl) "#Hg #HT";
      [rewrite -Heq //|rewrite Heq //]; by iApply "H".
  Qed.

  Lemma eq_to_bisub Γ T1 T2 i:
    (∀ ρ v, nclosed_vl v 0 → ⟦ T1 ⟧ ρ v ⊣⊢ ⟦ T2 ⟧ ρ v) → True ⊢
    Γ ⊨ [ T1, i ] <: [ T2, i ] ∗
    Γ ⊨ [ T2, i ] <: [ T1, i ].
  Proof.
    iIntros (Heq) "_"; iSplit; iIntros "/= !>" (ρ v Hcl) "#Hg #HT";
      [rewrite -Heq //|rewrite Heq //]; by iApply "H".
  Qed.

  Lemma selfIntersectLaterN Γ T U i j:
    Γ ⊨ [ T, i ] <: [ iterate TLater j U, i ] -∗
    Γ ⊨ [ T, i ] <: [ iterate TLater j (TAnd T U), i ].
  Proof.
    iIntros "H".
    setoid_rewrite (sub_rewrite_2 Γ T _ _ i (Distr_TLaterN_And T U j)).
    iApply (Sub_And with "[] H").
    iApply (Sub_Trans _ _ T _ _ (j + i)).
    - by iApply iterate_Sub_Mono.
    - by iApply iterate_Sub_Later.
  Qed.

  Lemma iterate_Later_Sub Γ T i j:
    Γ ⊨ [iterate TLater j T, i] <: [T, i + j].
  Proof.
      iInduction j as [] "IHj" forall (T); rewrite ?plusnO ?iterate_Sr ?plusnS.
    - iApply Sub_Refl.
    - iApply Sub_Trans.
      iApply ("IHj" $! (TLater T)).
      iApply Later_Sub.
  Qed.

  (* The point is, ensuring this works with T being a singleton type :-) *)
  Lemma dropLaters Γ e T U i:
    Γ ⊨ e : T -∗ Γ ⊨ [T, 0] <: [iterate TLater i U, 0] -∗
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
  Definition sem_singleton w ρ v : iProp Σ := (⌜ w.[to_subst ρ] = v ∧ nclosed_vl v 0 ⌝)%I.
  Arguments sem_singleton /.

  (* Core typing lemmas, sketches. TODO: make the above into a type, and add all
     the plumbing. *)
  Lemma self_sem_singleton ρ v: cl_ρ ρ → nclosed_vl v 0 → sem_singleton v ρ v.
  Proof.
    iIntros (Hclρ Hclv) "/= !%"; split => //. by apply closed_subst_vl_id.
  Qed.

  Lemma other_sem_singleton ρ w v v':
    (sem_singleton w ρ v →
    sem_singleton w ρ v' ↔ sem_singleton v ρ v')%I.
  Proof.
    iIntros ((Hv & Hclv)) "/="; iSplit; iIntros ((Hv1 & Hclv')) "!%"; split => //;
    by [> rewrite closed_subst_vl_id // -Hv -Hv1 | rewrite Hv -Hv1 closed_subst_vl_id ].
  Qed.

  Lemma tskip_self_sem_singleton ρ v: cl_ρ ρ → nclosed_vl v 0 →
    WP (tskip (tv v)) {{ v, sem_singleton v ρ v }}%I.
  Proof.
    iIntros (Hclρ Hclv) "/=".
    iApply wp_pure_step_later => //; iApply wp_value.
    iIntros "!%"; split => //. by apply closed_subst_vl_id.
  Qed.

  Lemma tskip_other_sem_singleton ρ w v v':
    sem_singleton w ρ v -∗
    WP (tskip (tv v)) {{ v', sem_singleton w ρ v' }}%I.
  Proof.
    iIntros (H); iApply wp_pure_step_later => //; iApply wp_value. by iIntros "!%".
  Qed.

  Fixpoint pth_to_tm p: tm :=
    match p with
    | pv v => tv v
    | pself p l => tproj (pth_to_tm p) l
    end.
  Definition sem_singleton_path p ρ v : iProp Σ := (□WP (pth_to_tm p).|[to_subst ρ] {{ w, ⌜ w = v ∧ nclosed_vl v 0 ⌝ }})%I.
  Arguments sem_singleton_path /.
  Lemma singletons_equiv w ρ v: sem_singleton w ρ v ⊣⊢ sem_singleton_path (pv w) ρ v.
  Proof.
    iSplit; iIntros "#H/=".
    - iModIntro. by iApply wp_value.
    - by iPoseProof (wp_value_inv with "H") as "H2".
  Qed.

  Lemma self_sem_singleton_path_v00 p i v:
    nclosed_vl v 0 → PureExec True i (pth_to_tm p) (tv v) →
    True ⊢ WP (pth_to_tm p) {{ sem_singleton_path p [] }}.
  Proof.
    iIntros (Hcl Hpure) "_ /=". rewrite to_subst_nil /=.
    iApply wp_pure_step_later => //.
    iNext.
    iApply wp_value. iModIntro.
    asimpl.
    iApply wp_pure_step_later => //.
    iNext.
    by iApply wp_value.
  Qed.


  (*
    We get. in fact, a chain of pure execution steps, each in a different world. IOW, a pure/path WP.
    It might be easier to define it directly (as path_wp) and prove typing rules for it,
    instead of trying to bridge across the two WP. *)
  Lemma step2 p ρ P:
    □WP (pth_to_tm p).|[to_subst ρ] {{ P }} -∗
    ∃ i, ▷^i ∃ v, ⌜ PureExec True i (pth_to_tm p).|[to_subst ρ] (tv v) ⌝ ∧ P v.
  Proof.
    iIntros "#H".
    iInduction p as [|] "IHp" forall (P); cbn.
    - iExists 0, (v.[to_subst ρ]). iPoseProof (wp_value_inv with "H") as "$".
      iPureIntro => ?. constructor.
    - iPoseProof (wp_bind_inv (fill [ProjCtx l]) with "H") as "H'"; rewrite /= /of_val.
      iDestruct ("IHp" with "H'") as (i0 v0) "[Hpure Hv]". iClear "IHp".
      Import uPred.
      iExists (S i0); rewrite laterN_later; iNext i0. iDestruct "Hpure" as %Hpure.
      iEval (rewrite !wp_unfold /wp_pre) in "Hv". cbn.
      iSpecialize ("Hv" $! inhabitant [] [] 0 with "[#//]"). iDestruct "Hv" as "[% Hv]". move: H => Hred.
      case: Hred => /= x [e' [σ' [efs Hred]]]. case Hred => /= K e1' e2' Heq1 Heq2 Hstp.
      have Heq: K = [].
      + eapply (ectxi_language_sub_redexes_are_values (tproj (tv v0) l)); [| apply Heq1| by eapply val_head_stuck].
        move=> Ki e2. move: Ki => []//=. move=>?[<-]?/=; eauto.
      + subst; cbn in *; subst.
        inverse Hstp.
        iSpecialize ("Hv" $! _ _ _ Hred). cbn.
        iExists w. iNext. iDestruct "Hv" as "[_ [Hv _]]".
        iPoseProof (wp_value_inv with "Hv") as "$".
        iPureIntro => ?. specialize (Hpure I).
        replace (S i0) with (i0+1) by lia.
        eapply (relations.nsteps_trans i0 1 _ (tproj (tv v0) l) _).
        by eapply (pure_step_nsteps_ctx (fill [ProjCtx l])).
        by eapply pure_tproj.
  Qed.
(*
  Lemma step2_v0 p ρ P:
    □WP (pth_to_tm p).|[to_subst ρ] {{ P }} -∗
    ∃ v i, ⌜ PureExec True i (pth_to_tm p).|[to_subst ρ] (tv v) ⌝ ∧  P v.
  Proof.
    iIntros "#H".
    iInduction p as [|] "IHp" forall (P); cbn.
    - iExists (v.[to_subst ρ]), 0. iPoseProof (wp_value_inv with "H") as "$".
      iPureIntro => ?. constructor.
    - iPoseProof (wp_bind_inv (fill [ProjCtx l]) with "H") as "H'"; rewrite /= /of_val.
      iDestruct ("IHp" with "H'") as (v0 i0) "[% Hv]". iClear "IHp". move: H => Hpure.
      iEval (rewrite !wp_unfold /wp_pre) in "Hv". cbn.
      iSpecialize ("Hv" $! inhabitant [] [] 0 with "[#//]"). iDestruct "Hv" as "[% Hv]". move: H => Hred.
      case: Hred => /= x [e' [σ' [efs Hred]]]. case Hred => /= K e1' e2' Heq1 Heq2 Hstp.
      have Heq: K = [].
      + eapply (ectxi_language_sub_redexes_are_values (tproj (tv v0) l)); [| apply Heq1| by eapply val_head_stuck].
        move=> Ki e2. move: Ki => []//=. move=>?[<-]?/=; eauto.
      + subst; cbn in *; subst.
        inverse Hstp.
        iSpecialize ("Hv" $! _ _ _ Hred). cbn.
        iExists v, (S i0).
        (* Okay, this is interesting, we get a later! *)
        iIntros (?).
  Admitted. *)

      (* iPoseProof (wp_value_inv with "Hv") as "?". *)

  Lemma self_sem_singleton_path_v01 p Γ T i v:
    Γ ⊨ pth_to_tm p : T -∗
    ⌜ PureExec True i (pth_to_tm p) (tv v) ⌝ .
  (* TODOs: demonstrate safety, demonstrate *)
  Abort.


  Lemma self_sem_singleton_path_v0 Γ p T i v:
    nclosed (pth_to_tm p) (length Γ) → PureExec True i (pth_to_tm p) (tv v) →
    True ⊢ ⌜ nclosed (pth_to_tm p) (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ → WP (pth_to_tm p).|[to_subst ρ] {{ sem_singleton_path p ρ }}.
  Proof.
    iIntros (Hcl Hpure) "_". iFrame "%". iIntros "!>" (ρ) "HG".
    iApply wp_pure_step_later. Fail eapply Hpure.
  Abort.

  Lemma self_sem_singleton_path Γ p T:
    Γ ⊨ pth_to_tm p : T -∗
    ⌜ nclosed (pth_to_tm p) (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ → WP (pth_to_tm p).|[to_subst ρ] {{ sem_singleton_path p ρ }}.
  Proof.
    iIntros "/= #[% #HT]". move: H => Hcl. iFrame (Hcl). iIntros "!>" (ρ) "#HG". iSpecialize ("HT" with "HG").
    iDestruct (interp_env_len_agree with "HG") as %Hlen. rewrite <- Hlen in *.
    iDestruct (interp_env_ρ_closed with "HG") as %Hclρ.

    iInduction p as [|] "IHp" forall (T Hcl); cbn.
    (* elim: p Hcl => [v|p IHp l] /= Hcl. *)
    (* iIntros "[$ #HT] !>" (ρ) "#HG"; iSpecialize ("HT" with "HG"). *)
    - iPoseProof (wp_value_inv with "HT") as "HvT".
      iDestruct (interp_v_closed with "HvT") as %?.
      iApply wp_value. iModIntro. by iApply wp_value.
    -
      iPoseProof (wp_bind_inv (fill [ProjCtx l]) with "HT") as "H"; rewrite /= /of_val.
      smart_wp_bind (ProjCtx l) w "Hw" "H".

      iApply (wp_wand with "Hw"). cbn. iIntros (v) "#Hv !>".
      smart_wp_bind (ProjCtx l) w' "Hw" "H".
      iApply (wp_wand with "Hw"). cbn. iIntros (v') "#Hv'".
      (* Print PureExec.
      Print pure_step. *)

      (* (* wwp_unfold /wp_pre
    iEval (rewrite !wp_unfold /wp_pre /=) in "HT".
 *)
      iApply (wp_bind (fill[(ProjCtx l)])).
      (* About wp_wand. *)
      (* : iProp Σ *)
      (* set foo : vl → iProp Σ := (λ v, WP (tproj (tv v) l) {{ w, ⟦ T ⟧ ρ w : iProp Σ }})%I. *)
      iApply (wp_wand _ _ _ (λ v, □WP tproj (tv v) l {{ w, ⟦ T ⟧ ρ w : iProp Σ }})%I). [iApply "H"; trivial|]; cbn;
      iIntros (v) Hv.

      smart_wp_bind (ProjCtx l) w "#Hw" "HT". *)
     Fail iApply wp_pure_step_later.
  Abort.


  (* From D.pure_program_logic Require Import weakestpre. *)

  Lemma ietp_later_works Γ W T v:
    W :: Γ ⊨ tv v : T -∗
    TLater W :: Γ ⊨ tv v: TLater T.
  Proof.
    iIntros "/= #[% #Hv]". move: H => Hclv. iFrame (Hclv). iIntros "!> *".
    destruct ρ as [|w ρ]; first by iIntros.
    iIntros "[#Hg [% #Hw]]". move: H => Hclw.
    iApply wp_value.
    iDestruct (interp_env_len_agree with "Hg") as %Hlen. rewrite <- Hlen in *.
    iDestruct (interp_env_ρ_closed with "Hg") as %Hclρ.
    have Hclvs: nclosed_vl v.[to_subst (w :: ρ)] 0.
      by apply fv_to_subst_vl; naive_solver eauto using fv_tv_inv.
    iFrame (Hclvs).
    iApply wp_value_inv'. iApply "Hv". by iSplit.
  Qed.

  Import uPred.
  Lemma internal_iff_eq_try1 (P Q: iProp Σ) `(!Affine P) `(!Affine Q): (P ↔ Q ⊢ P ≡ Q)%I.
  Proof.
    rewrite /bi_iff; unseal.
    constructor=> n x Hv [Hf1 Hf2].
    constructor=> n' x' Hle Hv'.
    have Hxl: x ≼ x' by admit. (* False, but needed below. *)
    split.
    - apply Hf1; first apply Hxl; done.
    - apply Hf2; first apply Hxl; done.
    all: fail.
  Abort.

  Lemma inclusion_equiv_wp_upd {P Q}:
    ((□∀ e, WP e {{P}} → WP e {{Q}})%I ≡ (□∀ v, P v → Q v)%I).
  Proof.
    iSplit; iIntros "#Himpl !> * HP".
    - setoid_rewrite wp_unfold.
        by iApply ("Himpl" $! (of_val v)).
    - iApply (wp_wand with " [-]"); first iApply "HP".
      iIntros "* HP". by iApply "Himpl".
  Qed.
End Sec.
