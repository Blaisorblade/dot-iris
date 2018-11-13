Require Import Dot.tactics.
Require Import Dot.unary_lr.

Section Sec.
  Context `{HdotG: dotG Σ}.

  Implicit Types T: ty.

  (* XXX can we use instead |={⊤}=> ⟦T1⟧ ρ v -∗ ⟦T2⟧ ρ v? What I have below arose from iStpUvstp,
     but a single modality seems more natural. However, using a single modality
     is stronger, and for the current definition of WP and subtyping, *too* strong. *)
  Definition uvstp1 Γ T1 T2: iProp Σ :=
    (□∀ ρ v, ⟦Γ⟧*ρ -∗ (|={⊤}=> ⟦T1⟧ ρ v) ={⊤}=∗ ⟦T2⟧ ρ v)%I.
  Global Arguments uvstp1 /.

  Definition uvstp2 Γ T1 T2: iProp Σ :=
    (□∀ ρ v, ⟦Γ⟧*ρ ={⊤}=∗ (⟦T1⟧ ρ v) → ⟦T2⟧ ρ v)%I.
  Global Arguments uvstp2 /.
  Print uvstp2.
  Lemma uvstp21 Γ T1 T2: (uvstp2 Γ T1 T2 → uvstp1 Γ T1 T2)%I.
  Proof.
    iIntros "/= #Hstp !> * #Hg".
    iDestruct ("Hstp" $! _ v with "Hg") as ">H".
    iIntros ">HT1 !>". by iApply "H".
  Qed.
  Notation "Γ ⊨> T1 <: T2" := (uvstp1 Γ T1 T2) (at level 74, T1, T2 at next level).

  (* False. *)
  Lemma uvstp12 Γ T1 T2: (uvstp1 Γ T1 T2 -∗ uvstp2 Γ T1 T2)%I.
  Proof.
    iIntros "/= #Hstp !> * #Hg".
    iSpecialize ("Hstp" $! ρ v with "Hg").
    Fail iMod "Hstp".
    Fail iApply "Hstp".
    iIntros "!>".
  Abort.

  Context (Γ: list ty).
  (** If we can prove that vstp and stp are equivalent, we can use them interchangeably; and in my previous proofs, proving vstp was much easier. *)
  Lemma iVstpStp T1 T2: (Γ ⊨ T1 <: T2 → Γ ⊨e T1 <: T2)%I.
  Proof.
    iIntros "/= #Hsub !> * #Hg HT1".
    iApply (wp_wand with " [-]"). iApply "HT1". by iIntros; iApply "Hsub".
  Qed.

  (* Does the converse direction hold? Do we need it? *)
  (* Lemma iStpVstp Γ T1 T2: (istp Γ T1 T2 -∗ ivstp Γ T1 T2)%I. *)
  (* This direction is useful when we have istp as an hypothesis. *)
  (* What I can easily prove: *)
  Lemma iStpUvstp T1 T2: (Γ ⊨e T1 <: T2 -∗ Γ ⊨> T1 <: T2)%I.
  Proof.
    (* Inspired by the proof of wp_value_inv'! *)

    (* More manual.*)
    (* iIntros "/= #Hsub !> * #Hg *". *)
    (* iSpecialize ("Hsub" $! (of_val v) with "Hg"). *)
    (* rewrite !wp_unfold /wp_pre /=. by iApply "Hsub". *)
    (* Restart. *)
    iIntros "/= #Hsub !> * #Hg *".
    setoid_rewrite wp_unfold.
    by iApply ("Hsub" $! (of_val v)).
  Qed.
  Implicit Types e: tm.
  (* To be able to use uvstp2, maybe we can use the following. Since it uses a single WP, it's clear
   * that we're talking about a single execution of e! That's weaker for non-deterministic
   * languages, but makes more sense: subtyping is about the same result after all.
   *)
  Definition istp2 Γ T1 T2 : iProp Σ := (□∀ e ρ, ⟦Γ⟧* ρ →
                                                 WP e {{v, ⟦T1⟧ ρ v → ⟦T2⟧ ρ v}})%I.
  Lemma iStpUvstp2 T1 T2: (istp2 Γ T1 T2 -∗ uvstp2 Γ T1 T2)%I.
  Proof.
    iIntros "/= #Hsub !> * #Hg *".
    iSpecialize ("Hsub" $! (of_val v) with "Hg").
    rewrite !wp_unfold /wp_pre /=. by iApply "Hsub".
  Qed.

  (* Maybe the update is OK; after all, it's part of the definition of weakest
     preconditions, and it pairs with the later. But it confuses me honestly.

     In any case, once we add pointers typing will clearly depend on resources (such as the heap), so we can just as well deal with it now. *)
  (* Also, subtyping now implies subtyping after update: *)
  Lemma vstpToUvstp T1 T2 : (Γ ⊨ T1 <: T2 → Γ ⊨> T1 <: T2)%I.
    iIntros "#Hstp !> * #Hg > HT1 !>".
    by iApply "Hstp".
  Qed.
  (* But not viceversa, because |==> P talks about the *existence* of a future resource world
   where P holds, even though P might be false now. *)
  Lemma uvstpToVstp T1 T2 : (Γ ⊨> T1 <: T2 → Γ ⊨ T1 <: T2)%I.
    iIntros "/= #Hstp !> * #Hg #Ht1".
    Fail iApply "Hstp".
  Abort.

  (* And subtyping later is enough to imply expression subtyping: *)
  Lemma iVstpUpdatedStp T1 T2: (Γ ⊨> T1 <: T2 → Γ ⊨e T1 <: T2)%I.
  Proof.
    iIntros "/= #Hstp !> * #Hg HeT1".
    by iApply (wp_strong_mono with "HeT1");
      last (iIntros "* HT1"; iApply "Hstp").
  Qed.

  Lemma ivstp_later G T: G ⊨ T <: TLater T.
  Proof. iIntros "!> ** /="; by iNext. Qed.

  (* So, value subtyping [ivstp] implies updated value subtyping [uvstp] but not
  viceversa. We can use the implication when proving value subtyping, but not
  when consuming its hypotheses. *)
  Lemma iuvstp_later T: Γ ⊨> T <: TLater T.
  Proof. iApply vstpToUvstp. iIntros "!> ** /="; by iNext. Qed.

  Lemma ivstp_ande1 T1 T2: Γ ⊨ TAnd T1 T2 <: T1.
  Proof. by iIntros "/= !> * ? [? ?]". Qed.
  Lemma ivstp_ande2 T1 T2: Γ ⊨ TAnd T1 T2 <: T2.
  Proof. by iIntros "/= !> * ? [? ?]". Qed.

  Lemma stp_andi T1 T2 ρ v:
    ⟦T1⟧ ρ v -∗
    ⟦T2⟧ ρ v -∗
    ⟦TAnd T1 T2⟧ ρ v.
  Proof. iIntros; by iSplit. Qed.

  Lemma ivstp_andi S T1 T2:
    Γ ⊨ S <: T1 -∗
    Γ ⊨ S <: T2 -∗
    Γ ⊨ S <: TAnd T1 T2.
  Proof.
    iIntros "/= #H1 #H2 !> * #Hg #HS".
    iApply stp_andi; [iApply "H1" | iApply "H2"]; done.
  Qed.

  Lemma stp_ori1 T1 T2 ρ v: ⟦T1⟧ ρ v -∗ ⟦TOr T1 T2⟧ ρ v.
  Proof. iIntros "? /="; by iLeft. Qed.
  Lemma stp_ori2 T1 T2 ρ v: ⟦T2⟧ ρ v -∗ ⟦TOr T1 T2⟧ ρ v.
  Proof. iIntros "? /="; by iRight. Qed.

  Lemma ivstp_ore S T1 T2:
    Γ ⊨ T1 <: S -∗
    Γ ⊨ T2 <: S -∗
    Γ ⊨ TOr T1 T2 <: S.
  Proof. iIntros "/= #H1 #H2 !> * #Hg #[HT1 | HT2]"; [iApply "H1" | iApply "H2"]; done. Qed.

  Lemma ivstp_ori1 T1 T2: Γ ⊨ T1 <: TOr T1 T2.
  Proof. iIntros "!> ** /="; by iLeft. Qed.
  Lemma ivstp_ori2 T1 T2: Γ ⊨ T2 <: TOr T1 T2.
  Proof. iIntros "!> ** /="; by iRight. Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂ᶻ
     ----------------------------------------------- (<:-μ-X)
     Γ ⊨ μ (x: T₁ˣ) <: μ(x: T₂ˣ)
  *)
  Lemma ivstp_mu_x T1 T2:
    ivstp (T1 :: Γ) T1 T2 -∗
    ivstp Γ (TMu T1) (TMu T2).
  Proof.
    iIntros "/= #Hstp !>" (v ρ) "#Hg #HT1".
    iApply ("Hstp" $! v (v :: ρ)); by try iSplit.
  Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂
     ----------------------------------------------- (<:-Bind-1)
     Γ ⊨ μ (x: T₁ˣ) <: T₂
  *)
  Lemma ivstp_mu_1 T1 T2:
    ivstp (T1 :: Γ) T1 (T2.[up_ty_vl var_vl]) -∗
    ivstp Γ (TMu T1) T2.
  Proof.
    iIntros "/= #Hstp !>" (v ρ) "#Hg #HT1".
    (* Hopefully from a renaming/weakening lemma. *)
    iAssert (interp T2 ρ v ≡ interp T2.[up_ty_vl var_vl] (v :: ρ) v)%I as "#Hren".
    { admit. }
    simpl.
    iRewrite "Hren".
    iApply ("Hstp" $! v (v :: ρ)); by try iSplit.
  Admitted.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ <: T₂ᶻ
     ----------------------------------------------- (<:-Bind-2)
     Γ ⊨ T₁ <: μ(x: T₂ˣ)
  *)
  Lemma ivstp_mu_2 T1 T2:
    ivstp (T1.[up_ty_vl var_vl] :: Γ) (T1.[up_ty_vl var_vl]) T2 -∗
    ivstp Γ T1 (TMu T2).
  Proof.
    iIntros "/= #Hstp !>" (v ρ) "#Hg #HT1".
    (* Hopefully from a renaming/weakening lemma. *)
    iAssert (interp T1 ρ v ≡ interp T1.[up_ty_vl var_vl] (v :: ρ) v)%I as "#Hren".
    { admit. }
    simpl.
    iRewrite "Hren" in "HT1".
    iApply ("Hstp" $! v (v :: ρ)); by try iSplit.
  Admitted.

  (* BEWARE NONSENSE IN NOTES:
     Γ ⊨ x: Tˣ
     ----------------------------------------------- (<:)
     Γ ⊨ mu(x: Tˣ) <: Tˣ    Γ ⊨ Tˣ <: mu(x: Tˣ)

     Luckily we don't need that, all the rules that exist before appear reasonable. *)

  (*
     Γ ⊨ z: Tᶻ
     =============================================== (T-Rec-I/T-Rec-E)
     Γ ⊨ z: mu(x: Tˣ)
   *)
  Lemma ivstp_rec_eq T v:
    ivtp Γ (TMu T) v ≡
    ivtp Γ T.[v/] v.
  Proof.
    iAssert (□ ∀ ρ, interp_env Γ ρ -∗ interp T.[v/] ρ v ≡ interp T (v :: ρ) v)%I as "#Hren".
    { admit. }
    iSplit; iIntros "/= #Htp !>" (ρ) "#Hg";
      iSpecialize ("Htp" $! ρ); iSpecialize ("Hren" $! ρ with "Hg").
    - iRewrite "Hren".
      by iApply "Htp".
    - iRewrite "Hren" in "Htp".
      by iApply "Htp".
  Admitted.

  Lemma ivstp_rec_i T v:
    ivtp Γ T.[v/] v -∗
    ivtp Γ (TMu T) v.
  Proof. by iDestruct ivstp_rec_eq as "[? ?]". Qed.

  Lemma ivstp_rec_e T v:
    ivtp Γ (TMu T) v -∗
    ivtp Γ T.[v/] v.
  Proof. by iDestruct ivstp_rec_eq as "[? ?]". Qed.
End Sec.
