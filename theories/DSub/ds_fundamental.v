(* This files proves the fundamental lemma for D<:.

   It also proves any typing lemmas that depend on swap_later_impl.v (extra
   modality swap lemmas, depending on `CmraSwappable` instances for Σ). They are
   kept separate, because we might have to extend Σ with resources without a
   CmraSwappable instance.
 *)
From iris.proofmode Require Import tactics.
From D Require Import proofmode_extra swap_later_impl.
From D.DSub Require Import ds_unary_lr ds_semtyp_lemmas.

Implicit Types (L T U : ty) (v : vl) (e : tm) (Γ : ctx).

Set Suggest Proof Using.
Set Default Proof Using "Type*".

Section swap_based_typing_lemmas.
  Context `{!dsubSynG Σ} `{!SwapPropI Σ} {Γ}.

  Lemma All_Sub_All T1 T2 U1 U2 i :
    Γ ⊨ T2, S i <: T1, S i -∗
    iterate TLater (S i) (shift T2) :: Γ ⊨ U1, S i <: U2, S i -∗
    Γ ⊨ TAll T1 U1, i <: TAll T2 U2, i .
  Proof.
    rewrite iterate_S /=.
    iIntros "#HsubT #HsubU /= %ρ %v #Hg".
    unfold_interp.
    iDestruct 1 as (t) "#[Heq #HT1]". iExists t; iSplit => //.
    iIntros (w).
    iSpecialize ("HsubT" $! ρ w with "Hg").
    rewrite -mlater_impl -mlaterN_impl !swap_later.
    iIntros "#HwT2".
    iSpecialize ("HsubT" with "HwT2").
    iAssert (▷ ▷^i (∀ v0, ⟦ U1 ⟧ (w .: ρ) v0 →
        ⟦ U2 ⟧ (w .: ρ) v0))%I as "{HsubU} #HsubU". {
      iIntros (v0); rewrite -!mlaterN_impl -mlater_impl.
      iIntros "#HUv0".
      iApply ("HsubU" $! (w .: ρ) v0 with "[# $Hg] HUv0").
      unfold_interp; rewrite iterate_TLater_later.
      by iApply (interp_weaken_one T2).
    }
    iNext 1; iNext i. iApply wp_wand.
    - iApply "HT1". by iApply "HsubT".
    - iIntros (u) "#HuU1". by iApply "HsubU".
  Qed.

  Lemma DSub_TAll_ConCov T1 T2 U1 U2 i :
    Γ ⊨[S i] T2 <: T1 -∗
    iterate TLater (S i) (shift T2) :: Γ ⊨[S i] U1 <: U2 -∗
    Γ ⊨[i] TAll T1 U1 <: TAll T2 U2.
  Proof.
    rewrite iterate_S /=.
    iIntros "#HsubT #HsubU /= %ρ #Hg %v".
    rewrite -mlaterN_impl; unfold_interp.
    iDestruct 1 as (t) "#[Heq #HT1]"; iExists t; iFrame "Heq".
    iIntros (w).
    rewrite -!laterN_later/= -!mlaterN_impl -!mlater_impl.
    iIntros "#HwT2".
    iSpecialize ("HsubT" with "Hg").
    iSpecialize ("HsubU" $! (w .: ρ) with "[# $Hg]"). {
      unfold_interp. rewrite iterate_TLater_later.
      by iApply (interp_weaken_one T2).
    }
    iNext 1; iNext i. iApply wp_wand.
    - iApply "HT1". by iApply "HsubT".
    - iIntros (u) "#HuU1". by iApply "HsubU".
  Qed.

  Lemma Typ_Sub_Typ L1 L2 U1 U2 i :
    Γ ⊨ L2, i <: L1, i -∗
    Γ ⊨ U1, i <: U2, i -∗
    Γ ⊨ TTMem L1 U1, i <: TTMem L2 U2, i.
  Proof.
    iIntros "#IHT #IHT1 /= %ρ %v #Hg".
    unfold_interp.
    iDestruct 1 as (φ) "#[Hφl [HLφ #HφU]]".
    setoid_rewrite mlaterN_impl.
    iExists φ; repeat iSplitL; first done;
      iIntros "" (w);
      iSpecialize ("IHT" $! ρ w with "Hg");
      iSpecialize ("IHT1" $! ρ w with "Hg");
      iNext; iIntros.
    - iApply "HLφ" => //. by iApply "IHT".
    - iApply "IHT1". by iApply "HφU".
  Qed.
End swap_based_typing_lemmas.

From D.DSub Require Import ds_storeless_typing.

Section Fundamental.
  Context `{!dsubSynG Σ} `{!SwapPropI Σ}.

  Lemma fundamental_subtype Γ T1 i1 T2 i2 (HT : Γ ⊢ₜ T1, i1 <: T2, i2) :
    ⊢ Γ ⊨ T1, i1 <: T2, i2
  with
  fundamental_typed Γ e T (HT : Γ ⊢ₜ e : T) :
    ⊢ Γ ⊨ e : T.
  Proof.
    - iInduction HT as [] "IHT".
      + by iApply Sub_Refl.
      + by iApply Sub_Trans.
      + by iIntros "/= **".
      + by iApply Sub_Index_Incr.
      + by iApply Later_Sub.
      + by iApply Sub_Later.
      + by iApply Sub_Top.
      + by iApply Bot_Sub.
      + iApply Sel_Sub. by iApply fundamental_typed.
      + iApply Sub_Sel. by iApply fundamental_typed.
      + by iApply All_Sub_All.
      + by iApply Typ_Sub_Typ.
    - iInduction HT as [] "IHT".
      + by iApply T_All_Ex.
      + by iApply T_All_E.
      + by iApply T_All_I.
      + by iApply T_Nat_I.
      + by iApply T_Var.
      + iApply T_ISub => //.
        by iApply fundamental_subtype.
      + iApply T_Vty_abs_I => //;
        by iApply fundamental_subtype.
    Qed.
End Fundamental.

From D.pure_program_logic Require Import adequacy.
From D.iris_extra Require Import det_reduction.

Theorem adequacy Σ `{HdsubG : dsubSynG Σ} `{!SwapPropI Σ} e T :
  (∀ `(dsubSynG Σ) `(SwapPropI Σ), ⊢ [] ⊨ e : T) →
  safe e.
Proof.
  rewrite /safe; intros Htyp ?*.
  cut (adequate e (λ _, True)); first by intros [_ ?]; eauto.
  eapply (wp_adequacy (Σ := Σ) e) => /=.
  iIntros "!>". iPoseProof (Htyp _ _) as "#Htyp".
  iSpecialize ("Htyp" $! ids with "[//]"); rewrite hsubst_id /=.
  iApply (wp_wand with "Htyp"); by iIntros.
Qed.

#[global] Instance dsubSynG_empty : dsubSynG #[] := {}.

Corollary type_soundness e T :
  [] ⊢ₜ e : T →
  safe e.
Proof.
  intros; eapply (adequacy #[]) => //; iIntros.
  by iApply fundamental_typed.
Qed.
