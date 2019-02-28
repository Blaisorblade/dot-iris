From iris.proofmode Require Import tactics.
From D Require Import tactics.
From D.Dot Require Import unary_lr typing synToSem lr_lemma.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

(* Should use fresh names. *)
Ltac iDestrConjs :=
  iMatchHyp (fun H P => match P with
                        | (_ ∧ _)%I =>
                          iDestruct H as "[#HA #HB]"
                        end).

Section fundamental.
  Context `{!dotG Σ}.
  Context `{hasStampTable: stampTable}.

  (** Show fundamental lemma. *)
  (** That depends on existence of translations. To use it, we must start from syntactic terms.
      So, we should show that syntactic typing only applies to syntactic terms/types/contexts
      (and probably add hypotheses to that effect). *)
  (* XXX lift translation and is_syn to contexts. Show that syntactic typing
     implies is_syn and closure. Stop talking about free variables inside is_syn? *)
  Lemma typed_tm_is_syn Γ e T:
    Γ ⊢ₜ e : T →
    is_syn_tm e.
  Admitted.

  Lemma typed_ty_is_syn Γ e T:
    Γ ⊢ₜ e : T →
    is_syn_ty T.
  Admitted.

  (* Check all types are syntactic. *)
  Definition is_syn_ctx Γ := Forall is_syn_ty Γ.

  Lemma typed_ctx_is_syn Γ e T:
    Γ ⊢ₜ e : T →
    is_syn_ctx Γ.
  Admitted.


  Lemma not_yet_fundamental Γ e T e' T' (HT: Γ ⊢ₜ e : T) {struct HT}:
  (* Lemma not_yet_fundamental Γ e T e' T' (HT: Γ ⊢ₜ e : T): *)
    (t_tm e e' → t_ty T T' → |==> Γ ⊨ e' : T')%I.
  Proof.
    iIntros "#HtrE #HtrT".
    (* destruct HT. *)
     iInduction HT as [] "IHT" forall (e' T') "HtrE HtrT".
  Admitted.

End fundamental.
