From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms)
         (Γ : ctx) (ρ : vls).

Section Russell.
  Context `{HdlangG: dlangG Σ}.

  (**
    A version of Russell's paradox, that however does not go through because of
    Iris's later.
    We define a value v such that testing v.A v is (almost) paradoxical, and would be
    paradoxical without Iris, because (informally) [v.A] points to [λ u, ¬ (u.A u)],
    hence [v.A v] is equivalent to ▷¬ (u.A u).
    *)
  Definition uAu u := ⟦TSel (pv u) "A"⟧ [] u.
  Instance uauP: Persistent (uAu u) := _.

  Definition russell_p : envD Σ := λ ρ v, (□ (uAu v -∗ False))%I.
  (* This would internalize as [russell_p ρ v := v : μ x. not (x.A)]. *)

  Context (s: stamp).

  Definition Hs := (s ↝ russell_p)%I.
  (** Under Iris assumption [Hs], [v.A] points to [russell_p].
      We assume [Hs] throughout the rest of the section. *)
  Definition v := vobj [("A", dtysem [] s)].

  (** Yes, v has a valid type member. *)
  Lemma vHasA: Hs -∗ ⟦ TTMem "A" TBot TTop ⟧ [] v.
  Proof.
    iIntros "#Hs". repeat (repeat iExists _; repeat iSplit; try done).
    iModIntro; repeat iSplit; by iIntros "** !>".
  Qed.

  Lemma later_not_UAU: Hs -∗ uAu v -∗ ▷ False.
  Proof.
    iIntros "#Hs #[_ Hvav]". rewrite /uAu.
    iDestruct "Hvav" as (φ d Hl) "[Hs1 Hvav]".
    iPoseProof "Hs1" as (s' σ φ' [Heq ->]) "H".
    iAssert (d ↗ (λ w, □ (uAu w -∗ False)))%I as "#Hs2".
    - subst d; move: Hl => [d] [[<-]] /= [?] ?; subst s' σ.
      iExists s, [], (λ ρ w, □ (uAu w -∗ False))%I.
      repeat iExists _; repeat iSplit => //.
    - iPoseProof (stored_pred_agree d _ _ v with "Hs1 Hs2") as "#Hag".
      iNext.
      iRewrite "Hag" in "Hvav"; iEval (cbn) in "Hvav".
      iApply "Hvav".
      repeat (repeat iSplit => //; repeat iExists _ => //).
  Qed.

  Lemma uauEquiv: Hs -∗ ▷ □ (uAu v -∗ False) ∗-∗ uAu v.
  Proof.
    iIntros "#Hs"; iSplit.
    - iIntros "#HnotVAV"; iSplit => //.
      iExists (russell_p []), (dtysem [] s).
      repeat (repeat iSplit => //; repeat iExists _).
      iIntros "!>!>!> #Hvav". iApply ("HnotVAV" with "Hvav").
    - iIntros "#Hvav".
      iPoseProof (later_not_UAU with "Hs Hvav") as "#HF".
      by iNext.
  Qed.

  (** uauEquiv would be absurd without later: a proposition
      can't be equivalent to its negation. *)
  Lemma taut0 (P: Prop): ((P → False) ↔ P) → False. Proof. tauto. Qed.
  (** But with later, there's no paradox — we get instead not (not P). *)
  Lemma irisTaut (P : iProp Σ):
    (▷ □ (P -∗ False) ∗-∗ P) -∗ □(P -∗ False) -∗ False.
  Proof. iIntros "Eq #NP". iApply "NP". by iApply "Eq". Qed.

  Lemma notNotVAV: Hs -∗ □ (uAu v -∗ False) → False.
  Proof.
    iIntros "#Hs #notVAV". iApply (irisTaut (uAu v)) => //.
    by iApply uauEquiv.
  Qed.

  Definition notRussellV: Hs -∗ russell_p [] v → False := notNotVAV.
End Russell.
