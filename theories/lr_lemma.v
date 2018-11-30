Require Import Dot.tactics.
Require Import Dot.unary_lr.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Section Sec.
  Context `{HdotG: dotG Σ}.

  Context (Γ: list ty).

  Lemma ivstp_later G T: G ⊨v T <: TLater T.
  Proof. by iIntros "!> ** /=". Qed.

  (* So, value subtyping [ivstp] implies updated value subtyping [uvstp] but not
  viceversa. We can use the implication when proving value subtyping, but not
  when consuming its hypotheses. *)
  Lemma iuvstp_later T: Γ ⊨> T <: TLater T.
  Proof. by iIntros "!> ** /=". Qed.

  Lemma ivstp_ande1 T1 T2: Γ ⊨> TAnd T1 T2 <: T1.
  Proof. by iIntros "/= !> * ? [? ?]". Qed.
  Lemma ivstp_ande2 T1 T2: Γ ⊨> TAnd T1 T2 <: T2.
  Proof. by iIntros "/= !> * ? [? ?]". Qed.

  (* Lemma stp_andi T1 T2 ρ v: *)
  (*   ⟦T1⟧ ρ v -∗ *)
  (*   ⟦T2⟧ ρ v -∗ *)
  (*   ⟦TAnd T1 T2⟧ ρ v. *)
  (* Proof. iIntros; by iSplit. Qed. *)

  Lemma ivstp_andi S T1 T2:
    Γ ⊨> S <: T1 -∗
    Γ ⊨> S <: T2 -∗
    Γ ⊨> S <: TAnd T1 T2.
  Proof.
    iIntros "/= #H1 #H2 !> * #Hg #HS".
    iSpecialize ("H1" with "Hg"); iMod ("H1" with "HS") as "#H1'".
    iSpecialize ("H2" with "Hg"); iMod ("H2" with "HS") as "#H2'".
    naive_solver.
  Qed.

  Lemma stp_ori1 T1 T2 ρ v: ⟦T1⟧ ρ v -∗ ⟦TOr T1 T2⟧ ρ v.
  Proof. iIntros "? /="; naive_solver. Qed.
  Lemma stp_ori2 T1 T2 ρ v: ⟦T2⟧ ρ v -∗ ⟦TOr T1 T2⟧ ρ v.
  Proof. iIntros "? /="; naive_solver. Qed.

  Lemma ivstp_ore S T1 T2:
    Γ ⊨> T1 <: S -∗
    Γ ⊨> T2 <: S -∗
    Γ ⊨> TOr T1 T2 <: S.
  Proof. iIntros "/= #H1 #H2 !> * #Hg #[HT1 | HT2]"; [iApply "H1" | iApply "H2"]; done. Qed.

  Lemma ivstp_ori1 T1 T2: Γ ⊨> T1 <: TOr T1 T2.
  Proof. iIntros "!> ** /="; naive_solver. Qed.
  Lemma ivstp_ori2 T1 T2: Γ ⊨> T2 <: TOr T1 T2.
  Proof. iIntros "!> ** /="; naive_solver. Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂ᶻ
     ----------------------------------------------- (<:-μ-X)
     Γ ⊨ μ (x: T₁ˣ) <: μ(x: T₂ˣ)
  *)
  Lemma ivstp_mu_x T1 T2:
    ivstp (T1 :: Γ) T1 T2 -∗
    ivstp Γ (TMu T1) (TMu T2).
  Proof.
    iIntros "/= #Hstp !> * #Hg #HT1".
    iApply ("Hstp" $! (v :: ρ) _); naive_solver.
  Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂
     ----------------------------------------------- (<:-Bind-1)
     Γ ⊨ μ (x: T₁ˣ) <: T₂
  *)

  Lemma ivstp_mu_1 T1 T2:
    ivstp (T1 :: Γ) T1 (T2.|[ren (+1)]) -∗
    ivstp Γ (TMu T1) T2.
  Proof.
    iIntros "/= #Hstp !> * #Hg #HT1".
    iApply (interp_weaken [] [v]).
    asimpl.
    iApply ("Hstp" $! (v :: ρ)); naive_solver.
  Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ <: T₂ᶻ
     ----------------------------------------------- (<:-Bind-2)
     Γ ⊨ T₁ <: μ(x: T₂ˣ)
  *)
  Lemma ivstp_mu_2 T1 T2:
    ivstp (T1.|[ren (+1)] :: Γ) (T1.|[ren (+1)]) T2 -∗
    ivstp Γ T1 (TMu T2).
  Proof.
    iIntros "/= #Hstp !> * #Hg #HT1".
    iAssert (⟦ T1.|[ren (+1)] ⟧ (v :: ρ) v)%I as "#HT1'".
    iApply (interp_weaken [] [v]); by iSimpl.
    iApply ("Hstp" $! (v :: ρ) _); by try iSplit.
  Qed.

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
    ((∀ ρ1 ρ2, (∀ x, x < length Γ → ρ1 x = ρ2 x) → v.[ρ1] = v.[ρ2]) ->
    ivtp Γ (TMu T) v ∗-∗
    ivtp Γ T.|[v/] v)%I.
  Proof.
    intros Hcl.
    assert (∀ ρ x, x < length Γ
             → to_subst ρ x = (to_subst ρ >> ren (+strings.length ρ)) x) as H.
    {
      (* Needed below: length Γ = length ρ *)
      asimpl.
      unfold to_subst.
      asimpl.
      admit.
    }
    iAssert (□(∀ ρ,
                 ⟦ T.|[v.[to_subst ρ]/] ⟧ ρ v.[to_subst ρ] ∗-∗ ⟦ T.|[v/] ⟧ ρ v.[to_subst ρ]))%I as "#Hren". admit.
    iSplit; iIntros "/= #Htp !> * #Hg";
      iSpecialize ("Htp" $! ρ with "Hg"); iSpecialize ("Hren" $! ρ);
      iPoseProof (interp_subst ρ T (v.[to_subst ρ]) (v.[to_subst ρ])) as "#Hren1"; asimpl; rewrite - (Hcl (to_subst ρ) ); try naive_solver.
    - iApply "Hren".
      iApply "Hren1".
      iApply "Htp".
    -
      iApply "Hren1".
      iApply "Hren".
      iApply "Htp".
  Admitted.

  (*   (* iIntros "#Hclosed". *) *)
  (*   iAssert (□ ∀ ρ, interp_env Γ ρ -∗ interp T.|[v/] ρ v.[to_subst ρ] ∗-∗ interp T (v.[to_subst ρ] :: ρ) v.[to_subst ρ])%I as "#Hren". *)
  (*   (* iAssert (□ ∀ ρ, interp_env Γ ρ -∗ interp T.|[v/] ρ v.[to_subst ρ] ≡ interp T (v :: ρ) v)%I as "#Hren". *) *)
  (*   { *)
  (*     iIntros "!> /= * #Hg". *)
  (*     iPoseProof (interp_subst ρ T (v.[to_subst ρ]) (v.[to_subst ρ])) as "#H". *)
  (*     iSplit; iIntros "#H2". *)
  (*     iApply "H". *)
  (*     asimpl. *)
  (*     rewrite - (Hcl (to_subst ρ) ). *)
  (*     rewrite - (Hcl ids). *)
  (*     rewrite - (Hcl ids (to_subst ρ) ). *)
  (*     asimpl. *)
  (*     iApply "H". *)
  (*   } *)

  (*     (* ("Hclosed" $! (to_subst ρ) ids) as "#H2". *) *)
  (*     (* iRewrite "#H2". *) *)

  (*     (* iPoseProof ("Hclosed" $! (to_subst ρ) ids) as "#H2". *) *)
  (*     (* iRewrite "#H2". *) *)
  (*   iSplit; iIntros "/= #Htp !> * #Hg"; *)
  (*     iSpecialize ("Htp" $! ρ); iSpecialize ("Hren" $! ρ with "Hg"). *)
  (*   -  *)
  (*     iApply "Hren". *)
  (*     by iApply "Htp". *)
  (*   - iApply "Hren". *)
  (*     by iApply "Htp". *)
  (* Qed. *)

  Lemma ivstp_rec_i T v:
    ((∀ ρ1 ρ2, (∀ x, x < length Γ → ρ1 x = ρ2 x) → v.[ρ1] = v.[ρ2]) ->
    ivtp Γ T.|[v/] v -∗
    ivtp Γ (TMu T) v).
  Proof. by intros; iDestruct ivstp_rec_eq as "[? ?]". Qed.

  Lemma ivstp_rec_e T v:
    ((∀ ρ1 ρ2, (∀ x, x < length Γ → ρ1 x = ρ2 x) → v.[ρ1] = v.[ρ2]) ->
    ivtp Γ (TMu T) v -∗
    ivtp Γ T.|[v/] v).
  Proof. by intros; iDestruct ivstp_rec_eq as "[? ?]". Qed.
End Sec.
