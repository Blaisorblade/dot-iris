(** * Exercise: Semantic typing for positive numbers (smallest example). *)
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting adequacy.
From iris.program_logic Require Import ectxi_language.

From D Require Import swap_later_impl.
From D.Dot Require Import ex_iris_utils.

From D.Dot.examples Require Import positive_div.
Import dlang_adequacy.

Set Suggest Proof Using.
Set Default Proof Using "Type".

Implicit Types (v w : vl) (d : dm) (ds : dms).

(** ** Example code. *)
Section examplesBodies.
  Import hoasNotation.
  Definition hminiV := ν: _, {@
    type "A" = 𝐙;
    val "n" = 2
  }.

  Definition hminiVT1 := μ: x, {@
    type "A" >: ⊥ <: 𝐙;
    val "n" : x @; "A"
  }.
End examplesBodies.

Section small_ex.
  Context `{HdlangG: !dlangG Σ} `{SwapPropI Σ}.

  Definition miniVT2Body : ty := {@
    type "A" >: ⊥ <: 𝐙;
    val "n" : TLater (x0 @; "A")
  }.
  Definition miniVT2 := μ miniVT2Body.

  Definition sminiVT2Body : oltyO Σ :=
    oAnd (oTMemL "A" oBot (oPrim tint))
      (oAnd (oVMem "n" (oLater (oSel x0 "A")))
      oTop).
  #[local] Lemma sminiVT2Body_test : V⟦miniVT2Body⟧ ≡ sminiVT2Body.
  Proof. done. Qed.

  Definition sminiVT2ConcrBody : cltyO Σ :=
    cAnd (cTMemL "A" ipos ipos)
      (cAnd (cVMem "n" (oLater (oSel x0 "A")))
      cTop).

  Lemma vHasA2t: ⊢ [] u⊨ hminiV : miniVT2.
  Proof using Type*.
    iApply (suT_Sub (T1 := oMu (c2o sminiVT2ConcrBody))); first last.
    - iApply sMu_Stp_Mu; rewrite oLaterN_0.
      iApply sStp_And; last iApply sStp_And; last iApply sStp_Top.
      + iApply sStp_Trans; [iApply sAnd1_Stp|iApply posTMem_widen].
      + iApply sStp_Trans; first iApply sAnd2_Stp.
        iApply sAnd1_Stp.
    - rewrite /hminiV /sminiVT2ConcrBody.
      iApply suT_Obj_I.
      iApply suD_Cons; [done| by iApply suD_posDm_ipos | ].
      iApply suD_Sing; iApply suD_Val.
      iApply (suT_Sub (T1 := ipos)).
      unstamp_goal_tm.
      by rewrite setp_value /ipos /pos; iIntros "!> %ρ _ /= !%"; naive_solver.
      iApply sStp_Trans; first iApply sStp_Add_Later.
      iApply sStp_Trans; first iApply sStp_Add_Later.
      iApply sLater_Stp_Eq.
      iApply sStp_Sel.
      iApply sP_Later.
      iApply sP_Sub; first by iApply sP_Var0.
      iApply sLater_Stp_Eq.
      iApply sAnd1_Stp.
  Qed.
End small_ex.

Lemma miniVSafe : safe hminiV.
Proof.
  apply (unstamped_safety_dot_sem dlangΣ (T := miniVT2))=>*.
  iApply vHasA2t.
Qed.
