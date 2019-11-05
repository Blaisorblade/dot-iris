From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language ectx_language ectxi_language.
From iris.proofmode Require Import tactics.
From D Require Import swap_later_impl.
From D.Dot Require Import unary_lr synLemmas rules
  lr_lemma lr_lemma_nobinding lr_lemmasDefs.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (p : path)
         (Γ : ctx).

Section Sec.
  Context `{HdlangG: dlangG Σ}.

  Lemma TAll_Later_Swap0 Γ T U `{SwapPropI Σ}:
    Γ ⊨ TAll (TLater T) U, 0 <: TLater (TAll T U), 0.
  Proof.
    iIntros "!>" (ρ v) "_ /= #HvTU".
    iDestruct "HvTU" as (t ->) "#HvTU".
    iExists t; iSplit => //. iNext.
    iIntros (w) "!>".
    rewrite -mlater_wand.
    iIntros "#HwT".
    by iApply ("HvTU" with "[# $HwT]").
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
    iApply (timeless with "H2"). admit.
    iSpecialize ("IH" with "H").
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
  Proof.
    iSplit.
    iIntros "/= [??]"; eauto.
    iIntros "/= [? ?]"; eauto.
  Qed.

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

  Definition sem_psingleton p ρ v : iProp Σ := path_wp p.|[ρ] (λ w, ⌜ w = v ⌝ )%I.
  Global Arguments sem_psingleton /.
  Global Instance: Persistent (sem_psingleton p ρ v) := _.

  Lemma psingletons_equiv w ρ v: sem_singleton w ρ v ⊣⊢ sem_psingleton (pv w) ρ v.
  Proof. done. Qed.

  Lemma self_sem_psingleton p ρ v :
    path_wp p.|[ρ] (λ w, ⌜ w = v ⌝) -∗ path_wp p.|[ρ] (sem_psingleton p ρ).
  Proof.
    iIntros "#Heq /=".
    iEval rewrite path_wp_eq. by iExists v; iFrame "Heq".
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
  Qed.

  (* Lemma nsteps_ind_r_weak `(R : relation A) (P : nat → A → A → Prop)
    (Prefl : ∀ x, P 0 x x) (Pstep : ∀ x y z n, relations.nsteps R n x y → R y z → P n x y → P (S n) x z) :
    ∀ x z n, relations.nsteps R n x z → P n x z.
  Proof.
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
