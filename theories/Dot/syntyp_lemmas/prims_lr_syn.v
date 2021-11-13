(** * Semantic lemmas for typing of primitive expressions. *)
From iris.proofmode Require Import tactics.
From D.Dot Require Import syn.
From D.Dot Require Import typing_aux_defs.
From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

From D.Dot Require Import unary_lr prims_lr.

Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms) (ρ : env).

Set Suggest Proof Using.
Set Default Proof Using "Type*".

Section Sec.
  Context `{HdlangG: !dlangG Σ}.

  Lemma P_Nat_I Γ n: ⊢ Γ ⊨p pv (vint n): TInt, 0.
  Proof. rw. apply sP_Nat_I. Qed.

  Lemma P_Bool_I Γ b: ⊢ Γ ⊨p pv (vbool b): TBool, 0.
  Proof. rw. apply sP_Bool_I. Qed.

  Lemma T_Un Γ u e1 B1 Br (Hu : un_op_syntype u B1 Br) :
    Γ ⊨ e1 : TPrim B1 -∗
    Γ ⊨ tun u e1 : TPrim Br.
  Proof. apply sT_Un, un_op_syntype_sound, Hu. Qed.

  Lemma T_Bin Γ b e1 e2 B1 B2 Br (Hu : bin_op_syntype b B1 B2 Br) :
    Γ ⊨ e1 : TPrim B1 -∗
    Γ ⊨ e2 : TPrim B2 -∗
    Γ ⊨ tbin b e1 e2 : TPrim Br.
  Proof. apply sT_Bin_cond, ty_syn, Hu. Qed.
End Sec.
