Require Import Dot.tactics.
Require Import Dot.unary_lr.
(* Require Import Dot.synLemmas. *)

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Section Sec.
  Context `{HdotG: dotG Σ}.

  Context (Γ: list ty).

  (** Show that inclusion between postconditions is equivalent to inclusion
      between value predicates *with an update modality. This is useful to show
      equivalent value and expression subtyping, both for a fixed environment and
      for environments matching a [Γ].
   *)
  Lemma inclusion_equiv_wp_upd {P Q}: ((□∀ e, WP e {{P}} → WP e {{Q}})%I ≡ (□∀ v, P v → |={⊤}=> Q v)%I).
  Proof.
    iSplit; iIntros "#Himpl !> * HP".
    - setoid_rewrite wp_unfold.
        by iApply ("Himpl" $! (of_val v)).
    - iApply wp_fupd.
      iApply (wp_wand with " [-]"); first iApply "HP".
      iIntros "* HP". by iApply "Himpl".
  Qed.

  Lemma mem_stp_sela_sub L U va l:
    ivtp Γ (TTMem l L U) va -∗
    Γ ⊨ L <: TSelA (pv va) l L U.
  Proof.
    iIntros "#Hva".
    rewrite istpEqIvstp.

    iIntros "/= !> * Hg #HvL".
    iDestruct ("Hva" $! ρ with "Hg") as (d) "#[% #H]"; iClear "Hva".
    iDestruct "H" as (φ σ) "#[Hl [#HLφ [#HφU #HLU]]]".
    iExists σ, φ, d.
    iDestruct ("HLφ" with "HvL") as "#HLφ'".
    iDestruct ("HLU" with "HvL") as "#HLU'".
    repeat iModIntro; repeat iSplit; trivial. by iRight.
  Qed.

  Lemma mem_stp_sel_sub L U va l:
    ivtp Γ (TTMem l L U) va -∗
    uvstp Γ (TLater L) (TSel (pv va) l).
  Proof.
    iIntros "/= #Hva !> * #Hg #HvL".
    iDestruct ("Hva" $! ρ with "Hg") as (d) "#[% #H]"; iClear "Hva".
    iDestruct "H" as (φ σ) "#[Hl [#HLφ [#HφU #HLU]]]".
    iExists σ , φ, d.
    iDestruct ("HLφ" with "HvL") as "#HLφ'".
    repeat iModIntro; repeat iSplit; trivial. by iRight.
  Qed.

  Instance Inh_vl: Inhabited vl.
  Proof. solve [repeat constructor]. Qed.
  (* Proof. constructor. exact (vabs (tv (var_vl 0))). Qed. *)
  Instance Inh_dm: Inhabited dm.
  Proof. solve [repeat constructor]. Qed.
  (* Proof. constructor. exact (dvl (inhabitant Inh_vl)). Qed. *)
  Instance Inh_vls: Inhabited vls.
  Proof. solve [repeat constructor]. Qed.

  Instance Inhϕ: Inhabited (list vl * vl → iProp Σ).
  Proof. constructor. exact (λ _, False)%I. Qed.

  (* Next step: proper lemma on arbitrary-length paths. *)
  Lemma mem_stp_sel_sub_path1 L U va l1 l2:
    (ivtp Γ (TVMem l1 (TTMem l2 L U)) va -∗
    uvstp Γ (TLater L) ((TSel (pself (pv va) l1) l2)))%I.
  Proof.
    iIntros "/= #Hva !> * #Hg #HvL".

    iDestruct ("Hva" $! ρ with "Hg") as (d) "#[% #Hvb]"; iClear "Hva".
    iDestruct "Hvb" as (vmem) "[-> H1]".
    iDestruct "H1" as (d) "[Hl2 H]".
    iDestruct "H" as (φ σ) "#[Hl [#HLφ [#HφU #HLU]]]".
    iDestruct ("HLφ" with "HvL") as "HLφ'".
    iExists vmem.
    repeat iModIntro; repeat iSplit; try done.
    iExists σ , φ, d.
    repeat iModIntro; repeat iSplit; try done.
    by iRight.
  Qed.


  (** Determinacy of obj_opens_to. *)
  Lemma objLookupDet v l d1 d2: v @ l ↘ d1 -> v @ l ↘ d2 -> d1 = d2.
  Proof.
    rewrite /objLookup; intros; ev; by subst; injectHyps; optFuncs_det.
  Qed.
  Ltac objLookupDet :=
    lazymatch goal with
    | H1: ?v @ ?l ↘ ?d1, H2: ?v @ ?l ↘ ?d2 |- _=>
      assert (d2 = d1) as ? by (eapply objLookupDet; eassumption); injectHyps
    end.

  Lemma mem_stp_sub_sel L U va l:
    ivtp Γ (TTMem l L U) va -∗
    uvstp Γ (TSel (pv va) l) (TLater U).
  Proof.
    iIntros "/= #Hva !> * #Hg #Hφ".
    iDestruct ("Hva" $! ρ with "Hg") as (d) "#[% #H]"; iClear "Hva".
    iDestruct "H" as (φ σ) "#[Hlφ [HLφ [HφU #HLU]]]".
    iDestruct "Hlφ" as (γ) "[% Hγφ]".

    iApply "HφU".
    iDestruct "Hφ" as (σ1 φ1 d1 Hva) "[Hγ [_ [False | #HΦ1v]]]"; try done.
    iDestruct "Hγ" as (γ' Hd1) "HγΦ1".

    injectHyps; objLookupDet; subst.

    iAssert (∀ ρ v, ▷ (φ ρ v ≡ φ1 ρ v))%I as "#Hag".
    { iIntros.
      (* fails T_T : iApply (saved_interp_agree_eta γ φ φ1 ρ0 v0). *)
      admit.
    }

    (* iAssert (▷ (subst_phi σ ρ φ v ≡ subst_phi σ ρ φ1 v))%I as "#Hag"; simpl. *)
    (*  ▷ (subst_phi σ ρ φ v ≡ subst_phi σ ρ φ1 v))%I as "#Hag". simpl. *)
    (* { qy iApply saved_pred_agree. } *)
    repeat iModIntro.
    inversion H1; subst.
    by iRewrite ("Hag" $! σ v).
  Admitted.
End Sec.
