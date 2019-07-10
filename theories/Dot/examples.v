From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr_binding
  lr_lemma lr_lemma_nobinding lr_lemmasDefs typeExtractionSem.

(** XXX Not currently using olty. *)
Module example.
Section ex.
  Context `{HdlangG: dlangG Σ}.

  Definition even v := ∃ n, v = vnat (2 * n).
  Definition ieven: envD Σ := λ ρ v, (⌜ even v ⌝) %I.
  Instance evenP ρ v: Persistent (ieven ρ v) := _.

  Context (s: stamp).

  Definition Hs := (s ↝ ieven)%I.
  (** Under Iris assumption [Hs], [v.A] points to [ieven].
      We assume [Hs] throughout the rest of the section. *)
  Definition v := vobj [("A", dtysem [] s); ("n", dvl (vnat 2))].

  Lemma sHasA : Hs -∗ def_interp_tmem ⟦ TBot ⟧ ⟦ TNat ⟧ ids (dtysem [] s).
  Proof.
    iIntros; repeat (repeat iExists _; repeat iSplit; try done).
    by iApply dm_to_type_intro.
    iModIntro; repeat iSplit; iIntros (w Hcl). by iIntros ">[]".
    iMod 1 as %[n ->]. eauto.
  Qed.

  (** Yes, v has a valid type member. *)
  Lemma vHasA0: Hs -∗ ⟦ TTMem "A" TBot TNat ⟧ ids v.
  Proof.
    iIntros "#Hs"; iSplit => //; iExists _; iSplit; by [eauto | iApply sHasA].
  Qed.

  (* Generic useful lemmas — not needed for fundamental theorem,
     but very useful for examples. *)
  Lemma ietp_value T v: nclosed_vl v 0 → ⟦ T ⟧ ids v -∗ [] ⊨ tv v : T.
  Proof.
    iIntros (?) "#H /="; iSplit; first by auto using fv_tv.
    iIntros "!>" (?->).
    rewrite -wp_value' to_subst_nil subst_id. iApply "H".
  Qed.

  Lemma ietp_value_inv T v: [] ⊨ tv v : T -∗ ⟦ T ⟧ ids v.
  Proof.
    iIntros "/= [% H]".
    iDestruct ("H" $! [] with "[//]") as "H".
    by rewrite wp_value_inv' subst_id.
  Qed.

  Lemma vHasA0': Hs -∗ [] ⊨ tv v : TTMem "A" TBot TNat.
  Proof.
    rewrite -ietp_value; by [iApply vHasA0|].
  Qed.

  (* This works. Crucially, we use TMu_I to introduce the object type.
     This way, we can inline the object in the type selection.
     This cannot be done using T_New_I directly.
     However, this is closer to how typechecking in Scala
     actually works.
     XXX: also, maybe this *could* be done with T_New_I with
     a precise type? That'd be a more correct derivation.
   *)
  Lemma vHasA1: Hs -∗
    ⟦ TMu (TAnd
          (TTMem "A" TBot TNat)
          (TAnd (TVMem "n" (TSel (pv (ids 0)) "A")) TTop)) ⟧ ids v.
  Proof.
    rewrite -ietp_value_inv -(TMu_I [] _ v).
    iIntros "#Hs".
    iApply TAnd_I; first by [iApply vHasA0'].
    iApply TAnd_I; first last.
    - iApply (T_Sub _ _ _ _ 0); last by iApply Sub_Top.
      by iApply vHasA0'.
    - rewrite -ietp_value /=; last done; iSplit => //.
      have Hev2: even (vnat 2). by exists 1.
      repeat (repeat iExists _; repeat iSplit);
        by [|iApply dm_to_type_intro].
  Qed.

  (*
    A different approach would be to type the object using T_New_I
    with an object type [U] with member [TTMem "A" ieven ieven].
    We could then upcast the object. But type U is not syntactic,
    so we can't express this yet using the existing typing
    lemmas.
    And if we use T_New_I on the final type, then [this.A]
    is overly abstract when we try proving that [this.n : this.A];
    see concretely below.
  *)
  Lemma vHasA1': Hs -∗
    ⟦ TMu (TAnd
          (TTMem "A" TBot TNat)
          (TAnd (TVMem "n" (TSel (pv (ids 0)) "A")) TTop)) ⟧ ids v.
  Proof.
    iIntros "#Hs".
    iDestruct (T_New_I [] _ with "[]") as "[% #H]"; first last.
    iSpecialize ("H" $! [] with "[#//]").
    rewrite to_subst_nil hsubst_id /interp_expr wp_value_inv'.
    iApply "H".
    iApply DCons_I => //.
    - (* Can't finish with D_Typ, this is only for syntactic types: *)

      (* iApply D_Typ => //.
      admit. admit. cbn. iSplit => //. iExists _; iSplit => //. *)
      iSplit => //=; iModIntro.
      iIntros ([|v ρ]) "/= #H". done.
      iDestruct "H" as "[-> [% _]]".
      iSplit => //. by iApply sHasA.
    - iApply DCons_I => //; last by iApply DNil_I.
      iApply TVMem_I.
      iSplit => //=.
      iIntros "!>" ([|v ρ]) "/= #H". done.
      iDestruct "H" as "[-> [[% HA] [[% HB] _]]]".
      rewrite -wp_value'; iSplit => //.
      iDestruct "HA" as (dA HlA φ) "[Hlφ HA]".
      iDestruct "HB" as (dB HlB w) "HB".
      iExists φ, dA; repeat iSplit => //.
      (* This will fail, since we don't know what v is and what
      "A" points to. *)
      Fail unfold v.
 Abort.
End ex.
End example.
