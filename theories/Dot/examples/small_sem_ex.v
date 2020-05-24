(** * Exercise: Semantic typing for positive numbers (smallest example). *)
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting adequacy.
From iris.program_logic Require Import ectxi_language.

From D Require Import swap_later_impl.
From D.Dot Require Import scala_lib hoas ex_utils storeless_typing_ex_utils ex_iris_utils.

From D.Dot.examples Require Import positive_div.
Import dlang_adequacy.

Set Suggest Proof Using.
Set Default Proof Using "Type".

Implicit Types (v w : vl) (d : dm) (ds : dms).

Import hoas.syn.

(** ** Example code. *)
Section examplesBodies.
  Import hoasNotation.
  Definition hminiV s := ν: _, {@
    type "A" = ([]; s);
    val "n" = 2
  }.

  Definition hminiVT1 := μ: x, {@
    type "A" >: ⊥ <: 𝐙;
    val "n" : x @; "A"
  }.
End examplesBodies.

Section small_ex.
  Context `{HdlangG: !dlangG Σ}.
  Context (s: stamp).

  Notation Hs := (s_is_pos s).
  Definition miniV : vl := hminiV s.
  (** Under Iris assumption [Hs], [miniV.A] points to [ipos]. *)

  (** Show that miniV has a valid type member. *)
  Lemma vHasA0typ: Hs -∗ [] ⊨ miniV : type "A" >: ⊥ <: 𝐙.
  Proof.
    iIntros "#Hs".
    iApply (T_Sub (i := 0) (T1 := μ {@ type "A" >: ⊥ <: 𝐙})); first last. {
      iApply Sub_Trans; first iApply (Mu_Sub {@ type "A" >: ⊥ <: 𝐙}).
      iApply sAnd1_Sub.
    }
    iApply T_Obj_I; iApply D_Cons; [done|iApply (sD_posDm_abs with "Hs")|].
    iSplit; last iIntros "!> ** "; naive_solver.
  Qed.

  (* This works. Crucially, we use T_Mu_I to introduce the object type.
     This way, we can inline the object in the type selection.
     This cannot be done using T_Obj_I directly.
     However, this is closer to how typechecking in Scala
     actually works.
     XXX: also, maybe this *could* be done with T_Obj_I with
     a precise type? That'd be a more correct derivation.
   *)
  Lemma vHasA1t : Hs -∗ [] ⊨ miniV : hminiVT1.
  Proof.
    rewrite -(T_Mu_I _ miniV).
    iIntros "#Hs /=".
    iApply sT_And_I; first by [iApply vHasA0typ].
    iApply sT_And_I; first last.
    - iApply (T_Sub (i := 0) (T2 := TTop)); last by iApply sSub_Top.
      by iApply vHasA0typ.
    - rewrite -setp_value_eq; iIntros (ρ).
      iExists _; iSplit; first naive_solver.
      rewrite oDVMem_eq path_wp_pv_eq oSel_pv.
      by iExists _, _; repeat iSplit; [naive_solver|
        by iApply dm_to_type_intro|rewrite /=/pos; eauto with lia].
  Qed.

  (*
    A different approach would be to type the object using T_Obj_I
    with an object type [U] with member [TTMem "A" ipos ipos].
    We could then upcast the object. But type U is not syntactic,
    so we can't express this yet using the existing typing
    lemmas.
    And if we use T_Obj_I on the final type, then [this.A]
    is overly abstract when we try proving that [this.n : this.A];
    see concretely below.
  *)
  Definition miniVT2Body : ty := {@
    type "A" >: ⊥ <: 𝐙;
    val "n" : TLater (x0 @; "A")
  }.
  Definition miniVT2 := μ miniVT2Body.

  Definition sminiVT2Body : oltyO Σ 0 :=
    oAnd (cTMem "A" oBot (oPrim tint))
      (oAnd (cVMem "n" (oLater (oSel x0 "A")))
      oTop).
  Goal V⟦miniVT2Body⟧ = sminiVT2Body. done. Abort.

  Definition sminiVT2ConcrBody : cltyO Σ :=
    cAnd (cTMem "A" ipos ipos)
      (cAnd (cVMem "n" (oLater (oSel x0 "A")))
      cTop).
  Definition sminiVT2Concr := oMu sminiVT2ConcrBody.

  (**
    The next lemma demonstrates an alternative typing derivation, using gDOT
    rules.
    But we get a weaker type, because we're using typing rules for recursive
    objects on a not-really-recursive one. *)
  Lemma vHasA2t `{SwapPropI Σ}: Hs -∗ [] ⊨ miniV : miniVT2.
  Proof.
    iIntros "#Hs".
    iApply (sT_Sub (i := 0) (T1 := sminiVT2Concr)); first last.
    - iApply sMu_Sub_Mu; rewrite /sminiVT2ConcrBody oLaterN_0.
      iApply sSub_And; last iApply sSub_And; last iApply sSub_Top.
      + iApply sSub_Trans; [iApply sAnd1_Sub|iApply posTMem_widen].
      + iApply sSub_Trans; first iApply sAnd2_Sub.
        iApply sAnd1_Sub.
    - rewrite /miniV /hminiV /sminiVT2Concr /sminiVT2ConcrBody.
      iApply sT_Obj_I.
      iApply sD_Cons; [done| by iApply (sD_posDm_ipos with "Hs") | ].
      iApply sD_Cons; [done| | by iApply sD_Nil].
      iApply sD_Val.
      iApply (sT_Sub (i := 0) (T1 := ipos)).
      by rewrite setp_value /ipos /pos; iIntros "!> %ρ _ /= !%"; naive_solver.
      iApply sSub_Trans; first iApply sSub_Add_Later.
      iApply sSub_Trans; first iApply sSub_Add_Later.
      iApply sSub_Later_Sub.
      iApply sSub_Sel.
      iApply sP_Later.
      iApply sP_Val.
      iApply (sT_Sub (i := 0)); first by iApply sT_Var0.
      iApply sSub_Later_Sub.
      iApply sAnd1_Sub.
  Qed.
End small_ex.

Lemma miniVSafe (s : stamp): safe (miniV s).
Proof.
  eapply (safety_dot_sem dlangΣ (T := hminiVT1))=>*.
  by rewrite (allocHs s) // -vHasA1t.
Qed.
