Require Import Dot.tactics.
Require Import Dot.unary_lr.

Section Sec.
  Context `{HdotG: dotG Σ}.

  Context (Γ: list ty).
  Implicit Types T: ty.

  Lemma ivstp_later G T: G ⊨ T <: TLater T.
  Proof. iIntros "!> ** /="; by iNext. Qed.

  Lemma ivstp_ande1 T1 T2: Γ ⊨ TAnd T1 T2 <: T1.
  Proof. by iIntros "/= !> * ? [? ?]". Qed.
  Lemma ivstp_ande2 T1 T2: Γ ⊨ TAnd T1 T2 <: T2.
  Proof. by iIntros "/= !> * ? [? ?]". Qed.

  Lemma stp_andi T1 T2 ρ v:
    ⟦T1⟧ ρ v -∗
    ⟦T2⟧ ρ v -∗
    ⟦TAnd T1 T2⟧ ρ v.
  Proof. iIntros; by iSplit. Qed.

  Lemma vstp_andi S T1 T2:
    vstp Γ S T1 ->
    vstp Γ S T2 ->
    vstp Γ S (TAnd T1 T2).
  Proof. move => /= H1 H2 v ρ Hg HS; by iSplit; [iApply H1 | iApply H2]. Qed.

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
    iApply "Hstp"; by try iSplit.
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
    iApply "Hstp"; by try iSplit.
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
    iApply "Hstp"; by try iSplit.
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
