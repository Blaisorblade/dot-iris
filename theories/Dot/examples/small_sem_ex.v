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
  Context `{HdlangG: !dlangG Σ} `{SwapPropI Σ}.
  Context (s: stamp).

  Notation Hs := (s_is_pos s).
  Definition miniV : vl := hminiV s.
  (** Under Iris assumption [Hs], [miniV.A] points to [ipos]. *)

  (** Show that miniV has a valid type member. *)
  Lemma vHasA0typ: Hs -∗ [] ⊨ miniV : type "A" >: ⊥ <: 𝐙.
  Proof.
    iIntros "#Hs".
    iApply (T_Sub (i := 0) (T1 := μ {@ type "A" >: ⊥ <: 𝐙})).
    iApply T_Obj_I.
    iApply D_Cons; [done| by iApply sHasA'|].
    iSplit; [iIntros "!%"|iIntros "!> ** //"]; first naive_solver.
    iApply Sub_Trans.
    iApply (Mu_Sub {@ type "A" >: ⊥ <: 𝐙}).
    iApply sAnd1_Sub.
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
    - rewrite -setp_value_eq /= /iPPred_car /=.
      have Hev2: pos (vint 2) by rewrite /pos; eauto with lia.
      iIntros (_).

      repeat (repeat iExists _; repeat iSplit; rewrite ?path_wp_pv_eq //);
        try by [|iApply dm_to_type_intro].
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

  Lemma sT_Var0 {Γ T}
    (Hx : Γ !! 0%nat = Some T):
    (*──────────────────────*)
    ⊢ Γ s⊨ x0 : T.
  Proof. rewrite -(hsubst_id T). apply (sT_Var Hx). Qed.

  (* The next lemma [ demonstrates an alternative typing derivation,
  using gDOT rules
   But we get a weaker type, because we're using typing rules
  for recursive objects on a not-really-recursive one. *)
  Lemma vHasA2t `{SwapPropI Σ}: Hs -∗ [] ⊨ miniV : miniVT2.
  Proof.
    iIntros "#Hs".
    iApply (sT_Sub (i := 0) (T1 := sminiVT2Concr)); first last.
    - iApply sMu_Sub_Mu; rewrite /sminiVT2ConcrBody oLaterN_0.
      iApply sSub_And; last iApply sSub_And; last iApply sSub_Top.
    + iApply sSub_Trans; first iApply sAnd1_Sub.
      iApply sTyp_Sub_Typ; [iApply sBot_Sub | iApply Sub_later_ipos_nat].
    + iApply sSub_Trans; first iApply sAnd2_Sub.
      iApply sAnd1_Sub.
    - rewrite /miniV /hminiV /sminiVT2Concr /sminiVT2ConcrBody.
      iApply sT_Obj_I.
      iApply sD_Cons; first done.
      iApply (sD_Typ_Abs ipos); [iApply sSub_Refl..|by iExists _; iFrame "Hs"].
      iApply sD_Cons; [done| |iApply sD_Nil].
      iApply sD_Val.
      iApply (sT_Sub (i := 0) (T1 := ipos)).
      rewrite setp_value /ipos /pos; iIntros "!> %ρ _ /= !%". naive_solver.
      iApply sSub_Trans; first iApply sSub_Add_Later.
      iApply sSub_Trans; first iApply sSub_Add_Later.
      iApply sSub_Later_Sub.
      iApply sSub_Sel.
      iApply sP_Later.
      iApply sP_Val.
      iApply (sT_Sub (i := 0)).
      by iApply sT_Var0.
      iApply sSub_Later_Sub.
      iApply sAnd1_Sub.
  Qed.
End small_ex.

Lemma miniVSafe (s : stamp): safe (miniV s).
Proof.
  eapply (safety_dot_sem dlangΣ (T := hminiVT1))=>*.
  by rewrite (allocHs s) // -vHasA1t.
Qed.
