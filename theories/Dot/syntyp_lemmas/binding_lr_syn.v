(** * Binding-related semantic typing lemmas. *)
From iris.proofmode Require Import tactics.

From D Require Import swap_later_impl.
From D.Dot Require Import unary_lr later_sub_syn.
From D.Dot Require Import binding_lr.

Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms) (ρ : env).

Set Suggest Proof Using.
Set Default Proof Using "Type*".
Set Implicit Arguments.
Unset Strict Implicit.

Section LambdaIntros.
  Context `{HdlangG: !dlangG Σ}.

  Lemma T_All_I_Strong {Γ Γ'} T1 T2 e
    (Hctx : ⊨G Γ <:* TLater <$> Γ') :
    shift T1 :: Γ' ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    rewrite /ietp fmap_cons (interp_commute_weaken_one T1).
    rewrite -(sT_All_I_Strong (Γ' := V⟦Γ'⟧*)) // => ρ.
    by rewrite -fmap_TLater_oLater.
  Qed.
End LambdaIntros.

Section Sec.
  Context `{HdlangG: !dlangG Σ}.

  Lemma P_Var {Γ x τ}
    (Hx : Γ !! x = Some τ):
    (*──────────────────────*)
    ⊢ Γ ⊨p pv (ids x) : shiftN x τ, 0.
  Proof.
    rewrite /iptp (interp_commute_weaken τ). apply sP_Var.
    by rewrite list_lookup_fmap Hx.
  Qed.

  Lemma T_All_Ex {Γ e1 v2 T1 T2}:
    Γ ⊨ e1: TAll T1 T2 -∗ Γ ⊨ tv v2 : T1 -∗ Γ ⊨ tapp e1 (tv v2) : T2.|[v2/].
  Proof. by rewrite /ietp (interp_commute_subst_one T2) -sT_All_Ex. Qed.

  Lemma T_All_E {Γ e1 e2 T1 T2} :
    Γ ⊨ e1 : TAll T1 (shift T2) -∗ Γ ⊨ e2 : T1 -∗ Γ ⊨ tapp e1 e2 : T2.
  Proof. by rewrite /ietp -sT_All_E -(interp_commute_weaken_one T2). Qed.
End Sec.
