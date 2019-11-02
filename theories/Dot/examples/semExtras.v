From iris.proofmode Require Import tactics.
From D Require Import swap_later_impl.
From D.Dot Require Import unary_lr.
(* synLemmas rules. *)

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (p : path)
         (Γ : ctx).

Section Sec.
  Context `{HdlangG: dlangG Σ}.

  Lemma map_TLater_env Γ ρ : ⟦ Γ ⟧* ρ -∗ ⟦ TLater <$> Γ ⟧* ρ.
  Proof. elim: Γ ρ => [//| T Γ IH] ρ; cbn; iIntros "[HG $]". by iApply IH. Qed.

  Context {Γ}.

  Lemma T_Forall_I' T1 T2 e:
    TLater T1.|[ren (+1)] :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "/= #HeT !>" (vs) "#HG".
    rewrite -wp_value'. iExists _; iSplit; first done.
    iIntros "!>" (v); rewrite -(decomp_s _ (v .: vs)).
    iIntros "!> #Hv".
    iApply ("HeT" $! (v .: vs) with "[$HG]").
    by rewrite (interp_weaken_one T1 _ v).
  Qed.

  Lemma wp_later_swap t Φ: WP t {{ v, ▷ Φ v }} ⊢ ▷ WP t {{ v, Φ v }}.
  Proof.
    iLöb as "IH" forall (t Φ).
    iEval (rewrite !wp_unfold /wp_pre /=).
    case: (to_val t) => [v|]. by eauto.
    iIntros "H" (σ1 κ κs n _); iDestruct ("H" $! σ1 κ κs n with "[#//]") as "[$ H]".
    iIntros (e2 σ2 efs Hstep); iDestruct ("H" $! e2 σ2 efs Hstep) as "[$ [H $]]".
    iApply ("IH" with "H").
  Qed.

  Lemma T_Forall_I'' T1 T2 e `{SwapPropI Σ}:
    TLater T1.|[ren (+1)] :: Γ ⊨ e : TLater T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "/= #HeT !>" (vs) "#HG".
    rewrite -wp_value'. iExists _; iSplitL; first done.
    iIntros "!>" (v); rewrite -(decomp_s e (v .: vs)).
    rewrite -wand_later; iIntros "#Hv".
    (* iApply (wp_later_swap _ (⟦ T2 ⟧ (v .: vs))).
    iApply ("HeT" $! (v .: vs) with "[$HG]"). *)
    iSpecialize ("HeT" $! (v .: vs) with "[$HG]").
    by rewrite (interp_weaken_one T1 _ v).
    iApply (wp_later_swap with "HeT").
  Qed.

  (** Stronger version of TAll_Later_Swap0, needs wp_later_swap, which
      might not extend to stronger WPs?*)
  Lemma TAll_Later_Swap `{SwapPropI Σ} T U i:
    Γ ⊨ TAll (TLater T) (TLater U), i <: TLater (TAll T U), i.
  Proof.
    iIntros "!>" (ρ v) "_ /= #HvTU". iNext i.
    iDestruct "HvTU" as (t ->) "#HvTU".
    iExists t; iSplit => //.
    iNext.
    iIntros (w); rewrite -mlater_wand; iIntros "!> #HwT".
    rewrite -(wp_later_swap _ (⟦ _ ⟧ _)).
    iApply (wp_wand with "(HvTU [# $HwT //])").
    by iIntros (v) "$".
  Qed.

  Lemma T_Forall_I_strange V T e:
    TLater <$> (V :: Γ) ⊨ e : T -∗
    (*─────────────────────────*)
    TLater V :: Γ ⊨ e : T.
  Proof.
    cbn; iIntros "#HeT !>" (ρ) "#HG".
    rewrite (map_TLater_env Γ).
    by iApply "HeT".
  Qed.

  Lemma T_Forall_I_strange2 V T1 T2 e:
    T1.|[ren (+1)] :: V :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    TLater V :: Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "/= #HeT !>" (vs) "#[HG HV]".
    rewrite -wp_value'. iExists _; iSplit; first done.
    iIntros "!>" (v); rewrite -(decomp_s _ (v .: vs)).
    iIntros "!> #Hv".
    iApply ("HeT" $! (v .: vs)); rewrite (interp_weaken_one T1 _ v) stail_eq.
    by iFrame "#".
  Qed.

  Lemma TVMem_All_I_derived V T1 T2 e l:
    T1.|[ren (+1)] :: V :: Γ ⊨ e : T2 -∗
    Γ |L V ⊨ { l := dvl (vabs e) } : TVMem l (TAll T1 T2).
  Proof.
    iIntros "/= #He !>" (ρ) "#Hg".
    iSplit => //; iExists (vabs _); iSplit => //.
    iApply wp_value_inv'.
    iApply (T_Forall_I_strange2 with "He [$Hg]").
  Qed.

  Lemma TVMem_All_I' V T1 T2 e l L:
    T1.|[ren (+1)] :: V :: Γ ⊨ e : T2 -∗
    TLater V :: Γ  ⊨ TAll T1 T2, 0 <: L, 0 -∗
    Γ |L V ⊨ { l := dvl (vabs e) } : TVMem l L.
  Proof.
    iIntros "#He #Hsub !>" (ρ); iEval (simpl); iIntros "#Hg".
    iSplit => //; iExists (vabs _); iSplit => //.
    iApply ("Hsub" with "Hg").
    iApply wp_value_inv'.
    iApply (T_Forall_I_strange2 with "He Hg").
  Qed.

End Sec.
