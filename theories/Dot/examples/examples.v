From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr
  lr_lemma lr_lemma_nobinding lr_lemmasDefs.

(** XXX Not currently using olty. *)
Module example.
Section ex.
  Context `{HdlangG: dlangG Σ}.

  Import stamp_transfer.

  Lemma alloc {s sγ} (φ : envD Σ) : sγ !! s = None → allGs sγ ==∗ s ↝ φ.
  Proof.
    iIntros (Hs) "Hsγ".
    by iMod (stamp_to_type_alloc φ Hs with "Hsγ") as (?) "[_ [_ $]]".
  Qed.

  Definition even v := ∃ n, v = vnat (2 * n).
  Definition ieven: envD Σ := λ ρ v, (⌜ even v ⌝) %I.
  Instance evenP ρ v: Persistent (ieven ρ v) := _.

  Context (s: stamp).

  Definition Hs := (s ↝ ieven)%I.
  Lemma allocHs sγ:
    sγ !! s = None → allGs sγ ==∗ Hs.
  Proof. exact (alloc ieven). Qed.

  (* Experiments using fancier infrastructure: *)
  Lemma allocHsGen sγ:
    sγ !! s = None → allGs sγ ==∗ Hs.
  Proof.
    iIntros (Hl) "H". iApply wellMappedφ_apply;
      last iApply (transfer (<[s:=ieven]> ∅) with "H") => s';
      rewrite ?lookup_insert ?dom_insert ?dom_empty //; set_solver.
  Qed.

  Lemma allocHs1: allGs ∅ ==∗ Hs.
  Proof.
    iIntros "H";  iApply wellMappedφ_apply; last iApply (transfer_empty (<[s:=ieven]> ∅) with "H").
    by rewrite lookup_insert.
  Qed.

  (** Under Iris assumption [Hs], [v.A] points to [ieven].
      We assume [Hs] throughout the rest of the section. *)
  Definition v := vobj [("A", dtysem [] s); ("n", dvl (vnat 2))].

  Lemma sHasA : Hs -∗ def_interp_tmem ⟦ TBot ⟧ ⟦ TNat ⟧ ids (dtysem [] s).
  Proof.
    iIntros; repeat (repeat iExists _; repeat iSplit; try done).
    by iApply dm_to_type_intro.
    iModIntro; repeat iSplit; iIntros (w). by iIntros ">[]".
    iMod 1 as %[n ->]. eauto.
  Qed.

  (** Yes, v has a valid type member. *)
  Lemma vHasA0: Hs -∗ ∀ ρ, ⟦ TTMem "A" TBot TNat ⟧ ρ v.[ρ].
  Proof.
    iIntros "#Hs" (ρ); iExists _; iSplit; by [eauto | iApply sHasA].
  Qed.

  (* Generic useful lemmas — not needed for fundamental theorem,
     but very useful for examples. *)
  Lemma ietp_value T v: (∀ ρ, ⟦ T ⟧ ρ v.[ρ]) -∗ [] ⊨ tv v : T.
  Proof.
    iIntros "#H /= !>" (? _).
    rewrite -wp_value'. iApply "H".
  Qed.

  Lemma ietp_value_inv T v: [] ⊨ tv v : T -∗ ∀ ρ, ⟦ T ⟧ ρ v.[ρ].
  Proof.
    iIntros "/= H" (ρ).
    iSpecialize ("H" $! ρ with "[//]").
    by rewrite wp_value_inv'.
  Qed.

  Lemma vHasA0typ: Hs -∗ [] ⊨ tv v : TTMem "A" TBot TNat.
  Proof. rewrite -ietp_value. iApply vHasA0. Qed.

  Definition vTyp1 :=
    TMu (TAnd
          (TTMem "A" TBot TNat)
          (TAnd (TVMem "n" (TSel (pv (ids 0)) "A")) TTop)).
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
    rewrite -ietp_value_inv -(TMu_I [] _ v).
    iIntros "#Hs".
    iApply TAnd_I; first by [iApply vHasA0typ].
    iApply TAnd_I; first last.
    - iApply (T_Sub _ _ _ _ 0); last by iApply Sub_Top.
      by iApply vHasA0typ.
    - rewrite -ietp_value /=.
      have Hev2: even (vnat 2). by exists 1.
      iIntros (_).
      repeat (repeat iExists _; repeat iSplit);
        by [|iApply dm_to_type_intro].
  Qed.

  Lemma vHasA1t : Hs -∗ [] ⊨ tv v : vTyp1.
  Proof. rewrite -ietp_value. iApply vHasA1. Qed.

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
  Lemma vHasA1': Hs -∗ ⟦ vTyp1 ⟧ ids v.
  Proof.
    iIntros "#Hs".
    iDestruct (T_New_I [] _ with "[]") as "#H"; first last.
    iSpecialize ("H" $! ids with "[#//]").
    rewrite hsubst_id /interp_expr wp_value_inv'.
    iApply "H".
    iApply DCons_I => //.
    - (* Can't finish with D_Typ_Abs, this is only for syntactic types: *)
      (* From D.Dot Require Import typeExtractionSem.
      iApply D_Typ_Abs => //; first last.
      iExists _; iSplit => //=.  (* Here we need a syntactic type matching [ieven]. *) *)
      iModIntro.
      iIntros (ρ) "/= #_".
      iSplit => //. by iApply sHasA.
    - iApply DCons_I => //; last by iApply DNil_I.
      iApply TVMem_I.
      iIntros "!>" (ρ) "/= #H /=".
      iDestruct "H" as "[_ [HA [HB _]]]".
      rewrite -wp_value'.
      iDestruct "HA" as (dA HlA φ) "[Hlφ HA]".
      iDestruct "HB" as (dB HlB w) "HB".
      iExists φ, dA; repeat iSplit => //.
      (* Stuck, since we don't know what [ρ 0] is and what
      "A" points to. *)
  Abort.

  Lemma vHasA1TypAd : allGs ∅ ==∗ [] ⊨ tv v : vTyp1.
  Proof. rewrite -ietp_value allocHs //; iIntros. by iApply vHasA1. Qed.
End ex.

Import dlang_adequacy swap_later_impl.
Lemma vSafe: safe (tv (v 1%positive)).
Proof. eapply (adequacy_dot_sem dlangΣ)=>*; apply vHasA1TypAd. Qed.
End example.
