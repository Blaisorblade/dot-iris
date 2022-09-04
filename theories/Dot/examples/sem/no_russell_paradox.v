(** * Russell's paradox does not affect guarded impredicative type members.
This is not in our paper.
- Naive impredicative type members support Russell's paradox (not shown here).
- The same problematic code, with guarded impredicative type members, is not a problem.
*)
From D.Dot Require Import unary_lr.

Implicit Types
         (L T U : ty) (v : vl) (e : tm) (d : dm) (ds : dms)
         (Γ : ctx).

Section Russell.
  Context `{HdlangG : !dlangG Σ}.

  (**
    A version of Russell's paradox, that however does not go through because of
    Iris's later.
    We define a value v such that testing v.A v is (almost) paradoxical, and would be
    paradoxical without Iris, because (informally) [v.A] points to [λ u, ¬ (u.A u)],
    hence [v.A v] is equivalent to ▷¬ (u.A u).
    *)
  Definition uAu u := oSel (pv u) "A" anil ids u.

  Definition russell_p : envD Σ := λI ρ v, uAu v -∗ False.
  (* This would internalize as [russell_p ρ v := v : μ x. not (x.A)]. *)

  Context (s : stamp).

  Definition Hs : iProp Σ := (s ↝n aopen russell_p).
  (** Under Iris assumption [Hs], [v.A] points to [russell_p].
      We assume [Hs] throughout the rest of the section. *)
  Definition v := vobj [("A", dtysem [] s)].

  Lemma uAu_unfold : uAu v ≡ vl_sel v "A" anil v.
  Proof. by rewrite /uAu/= !path_wp_pv_eq. Qed.

  (** Yes, v has a valid type member. *)
  Lemma vHasA : Hs ⊢ oTMem "A" oBot oTop anil ids v.
  Proof.
    rewrite oTMem_unfold. iIntros "#Hs".
    iExists _; iSplit. by iExists _; iSplit.
    iExists _; iSplit. by iApply dm_to_type_intro.
    by repeat iSplit; iIntros "% **".
  Qed.

  Lemma later_not_UAU : Hs ⊢ uAu v -∗ ▷ False.
  Proof.
    iIntros "Hs #HuauV".
    iPoseProof "HuauV" as "HuauV'".
    iEval (rewrite uAu_unfold) in "HuauV'".
    iDestruct "HuauV'" as (d ψ Hl) "[Hs1 Hvav]".
    have Hdeq : d = dtysem [] s. by move: Hl => /= [ds [[<- /=] ?]]; simplify_eq.
    iAssert (d ↗ aopen (russell_p ids)) as "#Hs2". by iApply (dm_to_type_intro with "Hs").
    iPoseProof (dm_to_type_agree anil v with "Hs1 Hs2") as "#Hag".
    (* without lock, iNext would strip a later in [HuauV]. *)
    rewrite [uAu]lock; iNext; unlock.
    iRewrite "Hag" in "Hvav".
    iApply ("Hvav" with "HuauV").
  Qed.

  Lemma uauEquiv : Hs ⊢ ▷ (uAu v -∗ False) ∗-∗ uAu v.
  Proof.
    iIntros "#Hs"; iSplit.
    - iIntros "#HnotVAV /=".
      iEval rewrite uAu_unfold.
      iExists (dtysem [] s), (aopen (russell_p ids)).
      repeat iSplit. {
        eauto using objLookupIntro.
      }
      + by iApply (dm_to_type_intro with "Hs").
      + iApply "HnotVAV".
    - iIntros "#Hvav".
      by iDestruct (later_not_UAU with "Hs Hvav") as "#>[]".
  Qed.

  (** uauEquiv would be absurd without later: a proposition
      can't be equivalent to its negation. *)
  Lemma taut0 (P : Prop) : ((P → False) ↔ P) → False. Proof. tauto. Qed.
  (** But with later, there's no paradox — we get instead not (not P). *)
  Lemma irisTaut (P : iProp Σ) :
    (▷ (P -∗ False) ∗-∗ P) -∗ (P -∗ False) -∗ False.
  Proof using Type*. iIntros "Eq #NP". iApply "NP". by iApply "Eq". Qed.

  Lemma notNotVAV : Hs ⊢ (uAu v -∗ False) → False.
  Proof.
    iIntros "#Hs #notVAV". iApply (irisTaut (uAu v)) => //.
    by iApply uauEquiv.
  Qed.

  Definition notRussellV : Hs ⊢ russell_p ids v → False := notNotVAV.
End Russell.
