Require Import Dot.unary_lr.
Require Import Dot.typing.
Require Import Dot.AAsynToSem.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

Section fundamental.
  Context `{dotG Σ}.

  (** Show fundamental lemma. *)
  (** That depends on existence of translations. To use it, we must start from syntactic terms.
      So, we should show that syntactic typing only applies to syntactic terms/types/contexts
      (and probably add hypotheses to that effect). *)
  (* XXX lift translation and is_syn to contexts. Show that syntactic typing
     implies is_syn and closure. Stop talking about free variables inside is_syn? *)
  Lemma typed_tm_is_syn Γ e T:
    Γ ⊢ₜ e : T →
    is_syn_tm (length Γ) e.
  Admitted.

  Lemma typed_ty_is_syn Γ e T:
    Γ ⊢ₜ e : T →
    is_syn_ty (length Γ) T.
  Admitted.

  (* Check all types are syntactic. The number of free varibles changes. Probably drop free variable count from is_syn_*. *)
  Definition is_syn_ctx Γ := True.

  Lemma typed_ctx_is_syn Γ e T:
    Γ ⊢ₜ e : T →
    is_syn_ctx Γ.
  Admitted.

  Theorem not_yet_fundamental Γ e T:
    Γ ⊢ₜ e : T →
    (|==> ∃ Γ' e' T',
          (* Using [] as σ is wrong. *)
        t_tm [] e e' ∗
        t_ty [] T T' ∗
        Γ' ⊨ e' : T')%I.
  Proof.
    intro HT.
    pose proof (typed_tm_is_syn Γ e T HT) as HeSyn.
    pose proof (typed_ty_is_syn Γ e T HT) as HTSyn.
    pose proof (typed_ctx_is_syn Γ e T HT) as HΓSyn.
    iMod (ex_t_tm [] (length Γ) e) as (e') "#HeTr"; first done.
    iMod (ex_t_ty [] (length Γ) T) as (T') "#HTTr"; first done.
    iExists Γ, e', T'. repeat iSplitL; try done.
    iInduction HT as []  "IHT" forall "HeTr HTTr".
                                      destruct e'; iDestruct "HeTr" as "HeTr'".
                                      simpl.
  Admitted.

End fundamental
