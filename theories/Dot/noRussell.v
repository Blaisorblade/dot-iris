From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms)
         (Γ : ctx).

Section Russell.
  Context `{HdlangG: dlangG Σ}.

  (**
    A version of Russell's paradox, that however does not go through because of
    Iris's later.
    We define a value v such that testing v.A v is (almost) paradoxical, and would be
    paradoxical without Iris, because (informally) [v.A] points to [λ u, ¬ (u.A u)],
    hence [v.A v] is equivalent to ▷¬ (u.A u).
    *)
  Definition uAu u := ⟦TSel (pv u) "A"⟧ ids u.
  Instance uauP: Persistent (uAu u) := _.

  Definition russell_p : envD Σ := λ ρ v, (□ (uAu v -∗ False))%I.
  (* This would internalize as [russell_p ρ v := v : μ x. not (x.A)]. *)

  Context (s: stamp).

  Definition Hs := (s ↝ russell_p)%I.
  (** Under Iris assumption [Hs], [v.A] points to [russell_p].
      We assume [Hs] throughout the rest of the section. *)
  Definition v := vobj [("A", dtysem [] s)].

  (** Yes, v has a valid type member. *)
  Lemma vHasA: Hs ⊢ ⟦ TTMem "A" TBot TTop ⟧ ids v.
  Proof.
    iIntros "#Hs /=".
    iSplit => //.
    repeat (repeat iExists _; repeat iSplit => //). by iApply dm_to_type_intro.
    iModIntro; repeat iSplit; by iIntros "** !>".
  Qed.

  Lemma later_not_UAU: Hs ⊢ uAu v -∗ ▷ False.
  Proof.
    iIntros "Hs #HuauV". rewrite /Hs /v.
    iPoseProof "HuauV" as (_ ψ d Hl) "[Hs1 Hvav]".
    have Hdeq: d = dtysem [] s. by move: Hl => /= [ds [[<- /=] ?]]; simplify_eq.
    iAssert (d ↗ russell_p ids) as "#Hs2". by iApply (dm_to_type_intro with "Hs").
    iPoseProof (dm_to_type_agree d _ _ v with "Hs1 Hs2") as "#Hag".
    (* without lock, iNext would strip a later in [HuauV]. *)
    rewrite /v [uAu]lock; iNext; unlock.
    iRewrite "Hag" in "Hvav".
    iApply ("Hvav" with "HuauV").
  Qed.

  Lemma uauEquiv: Hs ⊢ ▷ □ (uAu v -∗ False) ∗-∗ uAu v.
  Proof.
    iIntros "#Hs"; iSplit.
    - iIntros "#HnotVAV"; iSplit => //=.
      iExists (russell_p ids), (dtysem [] s).
      repeat iSplit; first by eauto.
      + by iApply (dm_to_type_intro with "Hs").
      + iIntros "!>!>!>". iApply "HnotVAV".
    - iIntros "#Hvav".
      by iDestruct (later_not_UAU with "Hs Hvav") as "#>[]".
  Qed.

  (** uauEquiv would be absurd without later: a proposition
      can't be equivalent to its negation. *)
  Lemma taut0 (P: Prop): ((P → False) ↔ P) → False. Proof. tauto. Qed.
  (** But with later, there's no paradox — we get instead not (not P). *)
  Lemma irisTaut (P : iProp Σ):
    (▷ □ (P -∗ False) ∗-∗ P) -∗ □(P -∗ False) -∗ False.
  Proof. iIntros "Eq #NP". iApply "NP". by iApply "Eq". Qed.

  Lemma notNotVAV: Hs ⊢ □ (uAu v -∗ False) → False.
  Proof.
    iIntros "#Hs #notVAV". iApply (irisTaut (uAu v)) => //.
    by iApply uauEquiv.
  Qed.

  Definition notRussellV: Hs ⊢ russell_p ids v → False := notNotVAV.
End Russell.
