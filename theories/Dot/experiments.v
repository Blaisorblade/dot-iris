From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language ectx_language ectxi_language.
From iris.proofmode Require Import tactics.
From D Require Import swap_later_impl.
From D.Dot Require Import unary_lr synLemmas rules
  lr_lemma lr_lemma_nobinding.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (p : path)
         (Γ : ctx).

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
    iApply (Sub_Trans _ T _ _ (S i)).
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
    iApply (Sub_Trans _ T _ _ (j + i)).
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

  Definition sem_psingleton p ρ v : iProp Σ := (□path_wp p.|[ρ] (λ w, ⌜ w = v ∧ nclosed_vl v 0 ⌝ ))%I.
  Global Arguments sem_psingleton /.

  Lemma psingletons_equiv w ρ v: sem_singleton w ρ v ⊣⊢ sem_psingleton (pv w) (to_subst ρ) v.
  Proof. iSplit; iIntros "#H /="; iApply "H". Qed.

  Lemma self_sem_psingleton p ρ v : ▷^(plength p) ⌜ nclosed_vl v 0 ⌝ -∗
    path_wp p.|[ρ] (λ w, ⌜ w = v ⌝) -∗ path_wp p.|[ρ] (sem_psingleton p ρ).
  Proof.
    iIntros "#Hcl #Heq /=".
    iEval rewrite path_wp_eq plength_subst_inv. iExists v; iFrame "Heq".
    iNext; iIntros "!>"; iDestruct "Hcl" as %Hcl.
    iEval rewrite path_wp_eq plength_subst_inv. eauto.
  Qed.

  Lemma T_self_sem_psingleton Γ p T i :
    (Γ ⊨p p : T , i) -∗
    (* (Γ ⊨p p : sem_psingleton p , i) *)
    (⌜ nclosed p (length Γ) ⌝ ∗
      □∀ vs, ⟦Γ⟧* vs →
      ▷^i path_wp (p.|[to_subst vs])
      (λ v, sem_psingleton p (to_subst vs) v)).
  Proof.
    iDestruct 1 as (Hclp) "#Hp". iFrame (Hclp).
    iIntros "!>" (vs) "#Hg".
    iSpecialize ("Hp" with "Hg"); iNext i.
    rewrite !path_wp_eq plength_subst_inv.
    iDestruct "Hp" as (v) "(Heq & Hcl)".
    iExists v; iFrame "Heq".
    iNext; iIntros "!>".
    rewrite interp_v_closed; iDestruct "Hcl" as %Hcl.
    iEval rewrite path_wp_eq plength_subst_inv. eauto.
  Qed.

  (* Lemma nsteps_ind_r_weak `(R : relation A) (P : nat → A → A → Prop)
    (Prefl : ∀ x, P 0 x x) (Pstep : ∀ x y z n, relations.nsteps R n x y → R y z → P n x y → P (S n) x z) :
    ∀ x z n, relations.nsteps R n x z → P n x z.
  Proof.
  Admitted.
    cut (∀ y z m n, relations.nsteps R n y z → ∀ x, relations.nsteps R m x y → P m x y → P (m + n) x z).
    admit.
    (* { eauto using relations.nsteps_0. } *)
    Search _ (_ + S _ = S (_ + _)).
    induction 1; rewrite /= ?Nat.add_0_r; eauto using nsteps_trans, nsteps_r.
    intros. eapply Pstep. [apply H1|..]. nsteps_r.
  Qed.
  *)

  (* Lemma self_sem_psingleton p:
    nclosed p 0 → path_wp p (sem_psingleton p []).
  Proof.
    elim: p => [v|p IHp l] /=; asimpl.
    by iIntros (Hcl%fv_pv_inv) "!> !%".

    iIntros (Hcl%fv_pself_inv). *)
    (* induction p. *)
  Lemma fv_pself_inv p l n: nclosed (pself p l) n → nclosed p n.
  Proof. solve_inv_fv_congruence. Qed.

  Lemma path_wp_exec2 {p v m} :
    PureExec True m (path2tm p) (tv v) →
    path_wp p (λ w, ⌜ w = v ⌝ : iProp Σ)%I.
  Admitted.
  Lemma self_sem_psingleton3 p i v:
    nclosed_vl v 0 → PureExec True i (path2tm p) (tv v) →
    path_wp p (sem_psingleton p ids).
  Proof.
    iIntros (Hcl Hexec) "/=".
    rewrite hsubst_id !path_wp_eq. iExists v.
    iDestruct (path_wp_exec2 Hexec) as "#H". iFrame "H".
    iIntros "!> !>". iEval rewrite path_wp_eq. eauto.
  Qed.

  Definition sem_singleton_path p ρ v : iProp Σ := (□WP (path2tm p).|[to_subst ρ] {{ w, ⌜ w = v ∧ nclosed_vl v 0 ⌝ }})%I.
  Arguments sem_singleton_path /.
  Lemma singletons_equiv w ρ v: sem_singleton w ρ v ⊣⊢ sem_singleton_path (pv w) ρ v.
  Proof.
    iSplit; iIntros "#H/=".
    - iModIntro. by iApply wp_value.
    - by iPoseProof (wp_value_inv with "H") as "H2".
  Qed.

  Lemma self_sem_singleton_path_v00 p i v:
    nclosed_vl v 0 → PureExec True i (path2tm p) (tv v) →
    True ⊢ WP (path2tm p) {{ sem_singleton_path p [] }}.
  Proof.
    iIntros (Hcl Hpure) "_ /=".
    rewrite -wp_pure_step_later // -wp_value hsubst_id.
    rewrite -wp_pure_step_later // -wp_value //.
  Qed.


  (*
    We get. in fact, a chain of pure execution steps, each in a different world. IOW, a pure/path WP.
    It might be easier to define it directly (as path_wp) and prove typing rules for it,
    instead of trying to bridge across the two WP. *)
  Lemma step2 p ρ P:
    □WP (path2tm p).|[to_subst ρ] {{ P }} -∗
    ∃ i, ▷^i ∃ v, ⌜ PureExec True i (path2tm p).|[to_subst ρ] (tv v) ⌝ ∧ P v.
  Proof.
    iIntros "#H".
    iInduction p as [|] "IHp" forall (P); cbn.
    - iExists 0, (v.[to_subst ρ]). iPoseProof (wp_value_inv with "H") as "$".
      iPureIntro => ?. constructor.
    - iPoseProof (wp_bind_inv (fill [ProjCtx l]) with "H") as "H'"; rewrite /= /of_val.
      iDestruct ("IHp" with "H'") as (i0 v0) "[Hpure Hv] {IHp}".
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
    □WP (path2tm p).|[to_subst ρ] {{ P }} -∗
    ∃ v i, ⌜ PureExec True i (path2tm p).|[to_subst ρ] (tv v) ⌝ ∧  P v.
  Proof.
    iIntros "#H".
    iInduction p as [|] "IHp" forall (P); cbn.
    - iExists (v.[to_subst ρ]), 0. iPoseProof (wp_value_inv with "H") as "$".
      iPureIntro => ?. constructor.
    - iPoseProof (wp_bind_inv (fill [ProjCtx l]) with "H") as "H'"; rewrite /= /of_val.
      iDestruct ("IHp" with "H'") as (v0 i0) "[% Hv] {IHp}". move: H => Hpure.
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
    Γ ⊨ path2tm p : T -∗
    ⌜ PureExec True i (path2tm p) (tv v) ⌝ .
  (* TODOs: demonstrate safety, demonstrate *)
  Abort.


  Lemma self_sem_singleton_path_v0 Γ p T i v:
    nclosed (path2tm p) (length Γ) → PureExec True i (path2tm p) (tv v) →
    True ⊢ ⌜ nclosed (path2tm p) (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ → WP (path2tm p).|[to_subst ρ] {{ sem_singleton_path p ρ }}.
  Proof.
    iIntros (Hcl Hpure) "_". iFrame "%". iIntros "!>" (ρ) "HG".
    iApply wp_pure_step_later. Fail eapply Hpure.
  Abort.

  Lemma self_sem_singleton_path Γ p T:
    Γ ⊨ path2tm p : T -∗
    ⌜ nclosed (path2tm p) (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ → WP (path2tm p).|[to_subst ρ] {{ sem_singleton_path p ρ }}.
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
    iIntros "/= #[% #Hv]". move: H => Hclv. iFrame (Hclv).
    iIntros "!>" ([|w ρ]); first by iIntros.
    iIntros "[#Hg [% #Hw]]". move: H => Hclw.
    rewrite -wp_value.
    iDestruct (interp_env_len_agree with "Hg") as %Hlen. rewrite <- Hlen in *.
    iDestruct (interp_env_ρ_closed with "Hg") as %Hclρ.
    have Hclvs: nclosed_vl v.[to_subst (w :: ρ)] 0.
      by apply fv_to_subst_vl; naive_solver eauto using fv_of_val_inv.
    iFrame (Hclvs).
    iApply wp_value_inv'. iApply "Hv". by iSplit.
  Qed.

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
