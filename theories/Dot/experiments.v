From iris.program_logic Require Import weakestpre lifting language ectx_lifting.
From iris.proofmode Require Import tactics.
From D Require Import tactics.
From D.Dot Require Import unary_lr unary_lr_binding synLemmas rules synToSem.
(* Workflow: Use this file for new experiments, and move experiments here in appropriate files once they're done. *)

(* From iris.bi Require Export derived_laws_bi. *)
(* From iris.bi Require Import derived_laws_sbi. *)
(* From iris.algebra Require Import monoid. *)

(* Module bi. *)
(* Import interface.bi. *)
(* Import derived_laws_bi.bi. *)
(* Import derived_laws_sbi.bi. *)

(* Section sbi_derived. *)
(* Context {PROP : sbi}. *)
(* Implicit Types φ : Prop. *)
(* Implicit Types P Q R : PROP. *)
(* About bi.internal_eq_rewrite'. *)
(* Hint Resolve internal_eq_refl. *)
(* (* Hint Extern 100 (NonExpansive _) => solve_proper. *) *)

(* Lemma internal_eq_iff P Q (_: Affine P) (_: Affine Q): (P ↔ Q ⊢ P ≡ Q)%I. *)
(* Proof. *)
(*   iIntros "H". *)
(*   iApply pure_internal_eq. *)
(*   About iff_equiv. *)
(*   pose proof (iff_equiv P Q) as Hf. *)
(*   iPoseProof (Hf with "H") as "Hf2". *)
(*   iApply Hf in "H". *)
(*   with "H"). *)
(*   iApply (iff_equiv P Q with "H"). *)
(*   Set Printing All. *)
(*   pose proof (proj2 (bi.equiv_spec P Q)). *)
(*   admit. *)
(*   SearchAbout bi_iff. *)
(*   iPureIntro. *)
(*   apply H. *)
(*   iDestruct "H" as "[H1 H2]". *)
(*   iDestruct  *)
(*   Set Printing All. *)
(*   iApply bi.equiv_spec. *)
(*       pose proof (proj2 (bi.equiv_spec (⟦ T' ⟧ ρ v) (⟦ T'' ⟧ ρ v))) as Heq. *)
(*       pose proof (proj2 (bi.equiv_spec (⟦ T' ⟧ ρ v) (⟦ T'' ⟧ ρ v))) as Heq. *)
(*   iSplit. *)
(*   OCheck internal_eq_rewrite'. *)
(*   apply (internal_eq_rewrite' P Q (λ Q, P ≡ Q))%I; auto using iff_refl. solve_proper. Qed. *)

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms)
         (Γ : ctx) (ρ : listVlC).

Module Russell.
Section Russell.
  Context `{HdotG: dotG Σ}.

  (** Russell's paradox, directly. *)
  Definition russell_p : listVlC -n> vlC -n> iProp Σ := λne ρ v, (⟦ TTMem "A" TBot TTop ⟧ [] v ∧ □ (⟦TSel (pv v) "A"⟧ [] v → False))%I.
  Context (γ: gname).
  Definition v := vobj [("A", dtysem [] γ)].

  Lemma taut0 (p: Prop): (p ↔(¬p))→ False. Proof. tauto. Qed.
  Lemma taut1 (p: Prop): (p ↔ ¬p)→ False.
  Proof.
    rewrite /not; intros [H0 H1].
    assert (H2notP: p → False). by intro H2p; apply H0; apply H2p.
    assert (H2p: p). by apply H1, H2notP.
    apply H2notP, H2p.
  Qed.

  Lemma vHasA: γ ⤇ (λ ρ v, russell_p ρ v) -∗ ⟦ TTMem "A" TBot TTop ⟧ [] v.
  Proof.
    iIntros "#Hγ". repeat (repeat iExists _; repeat iSplit; try done).
    iModIntro; repeat iSplit; by iIntros "**"; try iModIntro.
  Qed.

  Lemma notRussellV: γ ⤇ (λ ρ v, russell_p ρ v) -∗ □ (russell_p [] v → False).
    iIntros "#Hγ !> #[HvHasA #HnotRussellV]".
    (* Either: *)
    (* iApply "HnotRussellV". *)
    (* or some convolution to state the goal explicitly and explain what happens. *)
    iAssert (⟦ TSel (pv v) "A" ⟧ [] v) as "#HrussellV".
    2: {iApply "HnotRussellV". iApply "HrussellV". }

    iSplitL => //. iRight.
    iExists [], russell_p, (dtysem [] γ).
    repeat (repeat iExists _ ; repeat iSplit => //).
    iIntros "!>!>"; iSplit. iExact "HvHasA".
    iExact "HnotRussellV".
  Qed.
End Russell.
End Russell.

Section Sec.
  Context `{HdotG: dotG Σ}.

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

  Lemma tskip_self_sem_singleton ρ v: cl_ρ ρ → nclosed_vl v 0 → WP (tskip (tv v)) {{ v, sem_singleton v ρ v }}%I.
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

  Lemma ivtp_later Γ V T v:
    ivtp (V :: Γ) T v -∗
    ivtp (TLater V :: Γ) (TLater T) v.
  Proof.
    iIntros "/= #[% #Hv]". move: H => Hclv. iFrame (Hclv). iIntros "!> *".
    destruct ρ as [|w ρ]; first by iIntros.
    iIntros "[#Hg [% #Hw]]". move: H => Hclw.
    iSplit. {
      iPoseProof (interp_env_ρ_closed with "Hg") as "%". move: H => Hclρ.
      iPoseProof (interp_env_len_agree with "Hg") as "%". move: H => Hlen. rewrite <- Hlen in *.
      iPureIntro. apply fv_to_subst_vl; naive_solver.
    }
    iNext. iApply "Hv"; naive_solver.
  Qed.

  Lemma ietp_later_fails Γ W T v:
    W :: Γ ⊨ tv v : T -∗
    TLater W :: Γ ⊨ tv v: TLater T.
  Proof.
    iIntros "/= #[% #Hv]". move: H => Hclv. iFrame (Hclv). iIntros "!> *".
    destruct ρ as [|w ρ]; first by iIntros.
    iIntros "[#Hg [% #Hw]]". move: H => Hclw.
    iApply wp_value_fupd.
    iAssert ⌜nclosed_vl v.[to_subst (w :: ρ)] 0⌝%I as "%". {
      iPoseProof (interp_env_ρ_closed with "Hg") as "%". move: H => Hclρ.
      iPoseProof (interp_env_len_agree with "Hg") as "%". move: H => Hlen. rewrite <- Hlen in *.
      iPureIntro. apply fv_to_subst_vl; naive_solver eauto using fv_tv_inv.
    }
    move: H => Hclvs. iFrame (Hclvs).
    iSpecialize ("Hv" $! (w :: ρ)).

    iAssert (□(⟦ W ⟧ (w :: ρ) w → WP tv v.[to_subst (w :: ρ)] {{ v, ⟦ T ⟧ (w :: ρ) v }}))%I as "#Hv'". {
      iIntros "!> #Hw'". iApply "Hv". naive_solver.
    }
    iPoseProof ("Hv'" with "Hw") as "Hv2".
    iPoseProof (wp_value_inv with "Hv2") as "Hv3".

    iAssert (□ ▷ |={⊤}=> ⟦ W ⟧ (w :: ρ) w)%I as "#Hw''". naive_solver.
    iSpecialize ("Hv'" with "Hw''").
    iPoseProof (wp_value_inv with "Hv'") as "Hv4".

  (*   iSpecialize ("Hv" $! (w :: ρ)). *)
  (*   iApply wp_wand. iApply "Hv". *)
  (*   iNext. iApply "Hv"; naive_solver. *)
  (* Qed. *)
  Abort.

  Lemma ietp_later_futuremod Γ W T v:
    W :: Γ ⊨ tv v : T -∗
    (* Essentially [TLater W :: Γ ⊨ tv v: TLater T], but interpret TLater with
       the future modality. *)
         ⌜ nclosed (tv v) (length (W :: Γ)) ⌝ ∗
         □(∀ ρ w,
              ⟦Γ⟧* ρ →
              ⌜nclosed_vl w 0⌝ →
              (□ |={⊤}▷=> ⟦W⟧ (w :: ρ) w) →
                        WP (tv v.[to_subst (w :: ρ)])
                           {{ v0,
                              ⌜nclosed_vl v0 0⌝ ∗
                               |={⊤}▷=> ⟦T⟧ (w::ρ) v0 }}).
  Proof.
    iIntros "/= #[% #Hv]". move: H => Hclv. iFrame (Hclv). iIntros "!> *".
    iIntros "#Hg" (Hclw) "#Hw".
    iApply wp_value_fupd.
    iPoseProof (interp_env_ρ_closed with "Hg") as "%". move: H => Hclρ.
    iPoseProof (interp_env_len_agree with "Hg") as "%". move: H => Hlen. rewrite <- Hlen in *.
    have Hclvs: nclosed_vl v.[to_subst (w :: ρ)] 0.
      by apply fv_to_subst_vl; naive_solver eauto using fv_tv_inv.
    iFrame (Hclvs).
    iApply wp_value_inv'. iApply fupd_wp. iApply "Hv".
    iFrame "Hg". iExact "Hw".
  Qed.

  Definition idtp Γ T d : iProp Σ :=
    (⌜ nclosed d (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ → |={⊤}=> def_interp T ρ d.|[to_subst ρ])%I.
  Global Instance idtp_persistent Γ T d: Persistent (idtp Γ T d) := _.
  Notation "Γ ⊨d d : T" := (idtp Γ T d) (at level 64, d, T at next level).

  Lemma idtp_vmem_i' Γ W T v l:
    W :: Γ ⊨ tv v : T -∗
    TLater W :: Γ ⊨d dvl v : TVMem l T.
  Proof.
    iIntros "/= #[% #Hv]". move: H => Hclv. iSplit. auto using fv_tv_inv, fv_dvl. iIntros "!> *".
    destruct ρ as [|w ρ]; first by iIntros.
    cbn.
    iIntros "[#Hg [% #Hw]]". move: H => Hclw.
    iPoseProof (interp_env_ρ_closed with "Hg") as "%". move: H => Hclρ.
    iPoseProof (interp_env_len_agree with "Hg") as "%". move: H => Hlen. rewrite <- Hlen in *.

    have Hclvs: nclosed (dvl v.[to_subst (w :: ρ)]) 0. {
      apply fv_dvl; apply fv_to_subst_vl; naive_solver eauto using fv_tv_inv.
    }
    have Hrefl: dvl v.[to_subst (w :: ρ)] = dvl v.[to_subst (w :: ρ)]. done.
    iFrame (Hclvs).
    iExists v.[to_subst (w :: ρ)].
    iFrame (Hrefl).
    iSpecialize ("Hv" $! (w :: ρ)).

    iAssert (□ (⟦ W ⟧ (w :: ρ) w →
             WP tv v.[to_subst (w :: ρ)] {{ v, ⟦ T ⟧ (w :: ρ) v }}))%I as "#Hv'". {
      iIntros "!> #Hw'". iApply "Hv". naive_solver.
    }

    iAssert (□ (⟦ W ⟧ (w :: ρ) w →
             |={⊤}=> ⟦ T ⟧ (w :: ρ) (v.[to_subst (w :: ρ)])))%I as "#Hv''". {
      iIntros "!> #Hw'".
      iSpecialize ("Hv'" with "Hw'").
      iApply (wp_value_inv with "Hv'").
    }
    iSpecialize ("Hv''" with "Hw").
    (* iApply "Hv''". *)
    Abort.

  (*   iPoseProof (wp_value_inv with "Hv") as "Hv'". *)
  (*   iNext. *)
  (*   iAssert (⟦ V :: Γ ⟧* (w :: ρ)) as "HvHyp". naive_solver. *)
  (*   iSpecialize ("Hv" $! (w :: ρ) with "HvHyp"). iPoseProof (wp_value_inv with "Hv") as "Hv'". *)
  (*   iApply "Hv". naive_solver.. *)
  (* Qed. *)


  (* Lemma foo V T v: *)
  (*   ivtp (TLater V :: Γ) (TLater T) v -∗ *)
  (*   ivtp (V :: Γ) T v. *)
  (* Proof. *)
  (*   iIntros "#[% #Hv]". move: H => Hclv. iFrame (Hclv). iIntros "!> *". *)
  (*   destruct ρ as [|w ρ]; first by iIntros. iIntros "/= [#Hg #Hw]". *)
  (*   iAssert (⟦ Γ ⟧* ρ ∗ ⌜nclosed_vl w 0⌝ ∗ ▷ ⟦ V ⟧ (w :: ρ) w)%I as "#HvHyp". { *)
  (*     repeat iSplit => //. by iApply interp_v_closed. } *)
  (*   iDestruct ("Hv" $! (w :: ρ) with "HvHyp") as "[% H2]". *)
  (*   iApply "Hv". *)

  Lemma internal_iff_eq_try1 (P Q: iProp Σ) `(!Affine P) `(!Affine Q): (P ↔ Q ⊢ P ≡ Q)%I.
  Proof.
    constructor.
    remember (uPred_holds P) as P'. rewrite /uPred_holds in HeqP'.
    remember (uPred_holds Q) as Q'. rewrite /uPred_holds in HeqQ'.
    rewrite /uPredSI /sbi_internal_eq /= /bi_iff /= uPred_internal_eq_eq /uPred_internal_eq_def /uPred_holds /= /bi_and /= uPred_and_eq /uPred_and_def /= /bi_impl /= uPred_impl_eq /uPred_impl_def /= /uPred_holds.
    (* progress rewrite -HeqQ' -HeqP'. *)
    intros n x Hv [Hf1 Hf2]. constructor. intros n' x' Hle Hv'.
    assert (x ≼ x') as Hxl by admit. (* False, but needed below. *)
    split.
    - apply Hf1; first apply Hxl; done.
    - apply Hf2; first apply Hxl; done.
  Abort.

  Lemma translations_types_equivalent_vals T T' T'' v ρ:
    (t_ty T T' → t_ty T T'' → ⟦ T' ⟧ ρ v ≡ ⟦ T'' ⟧ ρ v)%I.
  Proof.
    (* -  *)
    (*   iIntros. *)
(*       Check uPred_primitive.equiv_spec. *)
(* (* From iris.base_logic Require Import upred. *) *)
(* (*       Import uPred. *) *)
(* (*       Check uPred. *) *)
(* From iris.bi Require Import bi. *)
(* Import bi. *)
(*       Check bi.equiv_spec . *)
(*       pose proof (proj2 (bi.equiv_spec (⟦ T' ⟧ ρ v) (⟦ T'' ⟧ ρ v))) as Heq. *)
(* From iris.bi Require Import derived_laws_sbi. *)
(*       Set Printing All. *)
(*       About internal_eq_iff. *)
(*       pose proof ((bi.internal_eq_iff (⟦ T' ⟧ ρ v) (⟦ T'' ⟧ ρ v))) as Heq1. *)
(*       Unset Printing All. *)
(*       iApply Heq. *)
(*       Locate "↔". *)
(*       SearchAbout and. *)
(*       destruct H1. *)
(*       pose proof (bi.equiv_spec (⟦ T' ⟧ ρ v) (⟦ T'' ⟧ ρ v)) as H1. *)
(*       iRewrite (bi_mixin_equiv_spec (⟦ T' ⟧ ρ v) (⟦ T'' ⟧ ρ v)). *)
(*       Set Printing All. *)
(*       SearchAbout (sbi_internal_eq). *)
(*       Set Printing All. *)
(*       SearchAbout uPred_entails. *)
(*       Check @bi.internal_eq_iff. *)
(*       Search *)
(*         (@bi_entails (sbi_bi _) (@sbi_internal_eq _ (sbi_ofeC _) _ _) (@bi_iff (sbi_bi _) _ _)). *)
(*       Require Import ssrbool. *)
(*       SearchHead sbi_internal_eq. *)
(*       Search "~~". *)
(*       Search (bi_entails (sbi_internal_eq _ _) (bi_iff _ _))%I. *)
(*       SearchPattern uPred_internal_eq. *)
(*       set (t := (@sbi_internal_eq (uPredSI (iResUR Σ)) (uPredC (iResUR Σ)))). *)
(*       hnf in t. *)
(*       Set Printing All. *)
(*        red. *)
(*        hnf. *)
(*        (ofe_mor_car _ _ (ofe_mor_car _ _ (@interp Σ H T') ρ) v) *)
(*              (ofe_mor_car _ _ (ofe_mor_car _ _ (@interp Σ H T'') ρ) v))). *)

    (* iInduction T as [] "IHT" forall (T' T'' ρ v); iIntros "#H1 #H2"; *)
    (*   destruct T' => //=; destruct T'' => //; cbn. *)
    (*                                 properness. *)
    (*                                 try (iDestruct "H1" as "[H11 H12]"); try (iDestruct "H2" as "[H21 H22]"). *)
    (* all: try iRewrite ("IHT" $! _ _ ρ v with "H11 H21"); try iRewrite ("IHT1" $! _ _ ρ v with "H12 H22"); try iRewrite ("IHT" $! _ _ ρ v with "H1 H2"); try done. *)
    (* - *)
    (*   iAssert (∀ ρ v, ⟦ T'1 ⟧ ρ v ≡ ⟦ T''1 ⟧ ρ v)%I as "#H". iIntros; iApply ("IHT"). *)
    (*   admit. *)
    (* - by iRewrite ("IHT" $! _ _ (v :: ρ) v with "H1 H2"). *)
    (* - *)
    (*   iDestruct "H11" as "->". *)
    (*   iDestruct "H21" as "->". *)
    (*   iAssert (∀ v, ⟦ T' ⟧ ρ v ≡ ⟦ T'' ⟧ ρ v)%I as "#H". by iIntros; iApply ("IHT"). *)
    (*   Fail iRewrite ("H" $! _). *)
    (*   admit. *)
  Abort.
    (*   iClear "H". *)
    (*   About (≡). *)
    (*   About sbi_internal_eq. *)
    (* Check (1 ≡ 2: iProp Σ)%I. *)
    (* Check bi_emp_valid. *)

    (*   red. *)
    (*   iEval (hnf). *)
    (*   iRewrite ("H" $! ρ). *)

    (* all: try iRewrite (IHT1 _ _ ρ v with "H11 H21"); try iRewrite (IHT2 _ _ ρ v with "H12 H22"); *)
    (* try iRewrite (IHT _ _ ρ v with "H1 H2"). *)
    (* all: try done. *)

    (* iPoseProof (IHT1 _ _ ρ v with "H11 H21") as "->". *)
    (* iPoseProof (IHT2 _ _ ρ v with "H11 H21") as "->". *)
    (* try iRewrite (IHT2 _ _ ρ v with "H12 H22"); *)
    (* admit. *)
    (* by iRewrite (IHT _ _ (v :: ρ) v with "H1 H2"). *)
    (* Check bi.sep_proper. *)
    (* - *)
    (*   About sbi_internal_eq. *)
    (*   Check sbi_internal_eq. *)
    (* Set Printing All. *)
    (* Check (1 ≡ 2)%I. *)
    (* Check bi_emp_valid. *)
    (* properness. *)
    (* iRewrite (IHT _ _ ρ with "H1 H2"). *)


  (* Can't find how to use it. *)
  Lemma later_persistently_1 (P: iProp Σ): (▷ □ P → ▷ P)%I.
  Proof. iIntros; naive_solver. Qed.

  (* (Expression) subtyping, strengthened to be equivalent to valye subtyping. *)
  Definition istp Γ T1 T2 : iProp Σ :=
    (ivstp Γ T1 T2 ∧ □∀ ρ e, ⟦Γ⟧* ρ → ⟦T1⟧ₑ ρ e → ⟦T2⟧ₑ ρ e)%I.
  Global Arguments istp /.

  Definition uvstp Γ T1 T2: iProp Σ :=
    (□∀ ρ v, ⟦Γ⟧*ρ -∗ ((*|={⊤}=>*) ⟦T1⟧ ρ v) → |={⊤}=> ⟦T2⟧ ρ v)%I.
  Global Arguments uvstp /.

  Notation "Γ ⊨e T1 <: T2" := (istp Γ T1 T2) (at level 74, T1, T2 at next level).
  Notation "Γ ⊨> T1 <: T2" := (uvstp Γ T1 T2) (at level 74, T1, T2 at next level).

  Definition uvstp2 Γ T1 T2: iProp Σ :=
    (□∀ ρ v, ⟦Γ⟧*ρ → |={⊤}=> (⟦T1⟧ ρ v) → ⟦T2⟧ ρ v)%I.
  Global Arguments uvstp2 /.
  (* Print uvstp2. *)

  (* To be able to use uvstp2, maybe we can use the following. Since it uses a single WP, it's clear
   * that we're talking about a single execution of e! That's weaker for non-deterministic
   * languages, but makes more sense: subtyping is about the same result after all.
   * However, this also asserts that all expressions are safe???
   *)
  Definition istp2 Γ T1 T2 : iProp Σ := (□∀ e ρ, ⟦Γ⟧* ρ →
                                                 WP e {{v, ⟦T1⟧ ρ v → ⟦T2⟧ ρ v}})%I.

  Lemma dropUpdateFromPremise {A B: iProp Σ}:
    (□ ((|={⊤}=> A) → |={⊤}=> B) ↔ □ (A → |={⊤}=> B))%I.
  Proof.
    iSplit; iIntros "#Himpl !>".
    - iIntros "HA". by iApply "Himpl".
    - iIntros ">HA". by iApply "Himpl".
  Qed.

  Context (Γ: list ty).

  (* Lemma iuvstp_later T: Γ ⊨> T <: TLater T. *)
  (* Proof. by iIntros "!> ** /=". Qed. *)

  Lemma istp2ivstp T1 T2: (Γ ⊨e T1 <: T2 → Γ ⊨ T1 <: T2)%I.
  Proof. by iIntros "/= [#? _]". Qed.

  Lemma ivstp2istp T1 T2: (Γ ⊨ T1 <: T2 → Γ ⊨e T1 <: T2)%I.
  Proof.
    iIntros "/= #Hstp". iFrame "Hstp".
    iIntros " !> * #Hg HeT1".
    iApply wp_fupd.
    iApply (wp_wand with " [-]"); try iApply "HeT1".
    iIntros "* HT1". by iApply "Hstp".
  Qed.


  (** We prove that vstp and stp are equivalent, so that we can use them
      interchangeably; and in my previous proofs, proving uvstp was easier. *)
  Lemma istpEqIvstp T1 T2: (Γ ⊨e T1 <: T2) ≡ (Γ ⊨ T1 <: T2).
  Proof. iSplit; iIntros; by [iApply istp2ivstp| iApply ivstp2istp]. Qed.

  Lemma iStpUvstp T1 T2: (Γ ⊨e T1 <: T2 → Γ ⊨> T1 <: T2)%I.
  Proof.
    (* Inspired by the proof of wp_value_inv'! *)

    (* More manual.*)
    (* iIntros "/= #Hsub !> * #Hg *". *)
    (* iSpecialize ("Hsub" $! (of_val v) with "Hg"). *)
    (* rewrite !wp_unfold /wp_pre /=. iIntros. by iApply "Hsub". *)
    (* Restart. *)
    iIntros "/= [#Hsub1 #Hsub2] !> * #Hg * #?".
    by iApply "Hsub1".
    (* Or *)
    (* setoid_rewrite wp_unfold. *)
    (* by iApply ("Hsub2" $! _ (of_val v)). *)
  Qed.



  (* Does the converse direction hold? Do we need it? *)
  (* Lemma iStpVstp Γ T1 T2: (istp Γ T1 T2 -∗ ivstp Γ T1 T2)%I. *)
  (* This direction is useful when we have istp as an hypothesis. *)
  (* What I can easily prove: *)

  Lemma vstpToUvstp T1 T2 : (Γ ⊨ T1 <: T2 → Γ ⊨> T1 <: T2)%I.
    iIntros "#Hstp !> * #Hg #HT1 !>".
    by iApply ("Hstp").
  Qed.

  Lemma iVstpStp T1 T2: (Γ ⊨ T1 <: T2 → Γ ⊨e T1 <: T2)%I.
  Proof. iApply ivstp2istp. Qed.
  (*   by iIntros "#Hsub"; iApply istpEqIvstp; iApply vstpToUvstp. *)
  (* Qed. *)
  (*   iIntros "#Hsub !> * #Hg HT1". *)
  (*   iApply (wp_wand with " [-]"). iApply "HT1". by iIntros; iApply "Hsub". *)
  (* Qed. *)

  (* Maybe the update is OK; after all, it's part of the definition of weakest
     preconditions, and it pairs with the later. But it confuses me honestly.

     In any case, once we add pointers typing will clearly depend on resources (such as the heap), so we can just as well deal with it now. *)
  (* Also, subtyping now implies subtyping after update: *)
  (* But not viceversa, because |==> P talks about the *existence* of a future resource world
   where P holds, even though P might be false now. *)
  Lemma uvstpToVstp T1 T2 : (Γ ⊨> T1 <: T2 → Γ ⊨ T1 <: T2)%I.
    iIntros "/= #Hstp !> * #Hg #Ht1".
    Fail iApply "Hstp".
  Abort.

  Lemma uvstp21 T1 T2: (uvstp2 Γ T1 T2 → uvstp Γ T1 T2)%I.
  Proof.
    iIntros "/= #Hstp !> * #Hg".
    iDestruct ("Hstp" $! ρ v with "Hg") as "H".
    iIntros "HT1". by iApply "H".
  Qed.

  (* False. *)
  Lemma uvstp12 T1 T2: (uvstp Γ T1 T2 -∗ uvstp2 Γ T1 T2)%I.
  Proof.
    iIntros "/= #Hstp !> * #Hg".
    iSpecialize ("Hstp" $! _ _ with "Hg").
    Fail iMod "Hstp".
    Fail iApply "Hstp".
    iIntros "!>".
  Abort.

  Lemma iStpUvstp2 T1 T2: (istp2 Γ T1 T2 -∗ uvstp2 Γ T1 T2)%I.
  Proof.
    iIntros "/= #Hsub !> * #Hg *".
    iSpecialize ("Hsub" $! (of_val v) with "Hg").
    rewrite !wp_unfold /wp_pre /=. by iApply "Hsub".
  Qed.

  Lemma inclusion_equiv_wp_upd {P Q}:
    ((□∀ e, WP e {{P}} → WP e {{Q}})%I ≡ (□∀ v, P v → |={⊤}=> Q v)%I).
  Proof.
    iSplit; iIntros "#Himpl !> * HP".
    - setoid_rewrite wp_unfold.
        by iApply ("Himpl" $! (of_val v)).
    - iApply wp_fupd.
      iApply (wp_wand with " [-]"); first iApply "HP".
      iIntros "* HP". by iApply "Himpl".
  Qed.
End Sec.
