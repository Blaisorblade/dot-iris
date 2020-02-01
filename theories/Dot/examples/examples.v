Import hoasNotation.
Module example.
Section ex.
  Context `{HdlangG: dlangG Σ}.
  Import swap_later_impl.
  (* Generic useful lemmas — not needed for fundamental theorem,
     but very useful for examples. *)

  Import hoasNotation.
  (** Under Iris assumption [Hs], [v.A] points to [ipos]. *)
  Import DBNotation.

  Definition v := ν {@
    type "A" = ([]; s);
    val "n" = pv (vnat 2)
  }.
  (** Yes, v has a valid type member. *)
  Arguments T_Sub {_ _ _ _ _ _ _}.
  Lemma vHasA0typ: Hs -∗ [] ⊨ tv v : type "A" >: ⊥ <: 𝐍.
  Proof.
    iIntros "#Hs".
    iApply (T_Sub (i := 0) (T1 := μ {@ type "A" >: ⊥ <: 𝐍})).
    iApply T_New_I.
    iApply DCons_I; [done| by iApply sHasA'|].
    iSplit; [iIntros "!%"|iIntros "!> ** //"].
    repeat constructor; exact: not_elem_of_nil.
    iApply Sub_Trans.
    iApply (Sub_Mu_A {@ type "A" >: ⊥ <: 𝐍}).
    iApply And1_Sub.
  Qed.

  Definition vTyp1Body : ty := {@
    type "A" >: ⊥ <: 𝐍;
    val "n" : p0 @; "A"
  }.
  Definition vTyp1 := μ vTyp1Body.

  (* This works. Crucially, we use TMu_I to introduce the object type.
     This way, we can inline the object in the type selection.
     This cannot be done using T_New_I directly.
     However, this is closer to how typechecking in Scala
     actually works.
     XXX: also, maybe this *could* be done with T_New_I with
     a precise type? That'd be a more correct derivation.
   *)
  Lemma vHasA1: Hs -∗ ∀ ρ, ⟦ vTyp1 ⟧ ρ v.[ρ].
  Proof.
    rewrite -ietp_value_inv -(TMu_I _ v).
    iIntros "#Hs".
    iApply TAnd_I; first by [iApply vHasA0typ].
    iApply TAnd_I; first last.
    - iApply (T_Sub (i := 0)); last by iApply Sub_Top.
      by iApply vHasA0typ.
    - rewrite -setp_value_eq /= /iPPred_car /=.
      have Hev2: pos (vnat 2) by rewrite /pos; eauto.
      iIntros (_).

      repeat (repeat iExists _; repeat iSplit; rewrite ?path_wp_pv //);
        try by [|iApply dm_to_type_intro].
  Qed.

  Lemma vHasA1t : Hs -∗ [] ⊨ tv v : vTyp1.
  Proof. rewrite -ietp_value. iApply vHasA1. Qed.

  Lemma vHasA1TypAd : allGs ∅ ==∗ [] ⊨ tv v : vTyp1.
  Proof. rewrite -ietp_value allocHs //; iIntros. by iApply vHasA1. Qed.

  (* Lemma vHasA1': Hs -∗ ∀ ρ, ⟦ vTyp1 ⟧ ρ v.[ρ].
  Proof.
    rewrite -ietp_value_inv. iIntros "#Hs".
    (* Fails, because we need a *syntactic* type. *)
    iApply (T_Sub [] v _ vTyp1 0). *)

  (*
    A different approach would be to type the object using T_New_I
    with an object type [U] with member [TTMem "A" ipos ipos].
    We could then upcast the object. But type U is not syntactic,
    so we can't express this yet using the existing typing
    lemmas.
    And if we use T_New_I on the final type, then [this.A]
    is overly abstract when we try proving that [this.n : this.A];
    see concretely below.
  *)
  Lemma vHasA1': Hs -∗ ⟦ vTyp1 ⟧ ids v.
  Proof.
    iIntros "#Hs".
    iDestruct (T_New_I [] vTyp1Body with "[]") as "#H"; first last.
    iSpecialize ("H" $! ids with "[#//]").
    rewrite hsubst_id /interp_expr wp_value_inv'.
    iApply "H".
    iApply DCons_I => //.
    - (* Can't finish with D_Typ_Abs, this is only for syntactic types: *)
      (* From D.Dot Require Import typeExtractionSem.
      iApply D_Typ_Abs => //; first last.
      iExists _; iSplit => //=.  (* Here we need a syntactic type matching [ipos]. *) *)
      iModIntro.
      iIntros (ρ Hpid) "/= #_".
      iSplit => //. by iApply sHasA.
    - iApply DCons_I => //; last by iApply DNil_I.
      iApply D_Path_TVMem_I.
      iIntros "!>" (ρ) "/="; iDestruct 1 as "[_ [HA [HB _]]]".
      iDestruct "HA" as (dA) "[HlA HA]".
      iDestruct "HA" as (φ) "[Hlφ HA]".
      iDestruct "HB" as (dB) "[HlB HB]".
      iDestruct "HB" as (w) "HB".
      rewrite !path_wp_pv.
      iExists φ, dA; repeat iSplit => //; try iNext => //.
      (* Last case is stuck, since we don't know what [ρ 0] is and what
      "A" points to. *)
  Abort.

  (* Lemma vHasA1': Hs -∗ ∀ ρ, ⟦ vTyp1 ⟧ ρ v.[ρ].
  Proof.
    rewrite -ietp_value_inv. iIntros "#Hs".
    (* Fails, because we need a *syntactic* type. *)
    iApply (T_Sub [] v _ vTyp1 0). *)

End ex.

Import dlang_adequacy swap_later_impl.
Lemma vSafe: safe (tv (v 1%positive)).
Proof. eapply (safety_dot_sem dlangΣ)=>*; apply vHasA1TypAd. Qed.
End example.
