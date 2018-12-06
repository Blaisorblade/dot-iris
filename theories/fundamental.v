From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import tactics.
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

  Fixpoint not_yet_fundamental Γ e T:
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
    (* (* XXX using the translation here means we end up using it again later, and *)
    (*    we'd even have to prove it's deterministic (which it isn't?) or smth. such! *)
    (*    Let's avoid that. *) *)
    (* iMod (ex_t_tm [] (length Γ) e) as (e') "#HeTr"; first done. *)
    (* iMod (ex_t_ty [] (length Γ) T) as (T') "#HTTr"; first done. *)
    (* iExists Γ, e', T'. repeat iSplitL; try done. *)
    (* Induction keeps the same expression e' in the conclusion of *all* induction hypotheses. *)
    (* iInduction HT as []  "IHT" forall "HeTr HTTr". *)
    (* So use destruct and a recursive proof; we'll need this anyway since the
       proof is by mutual induction on typing, subtyping etc.*)
    destruct HT.
    (* iDestruct HT as ([]) "". "IHT" forall "HeTr HTTr". *)
    -
      (* Arguments t_tm _ _ _ /. *)
      (* Arguments t_vl _ _ _ /. *)

      (* destruct e'; cbn [t_tm]; try done. *)
      (* fold (t_tm [] e1 e'1). *)
      (* fold (t_tm [] (tv v2) e'2). *)
      (* iDestruct "HeTr" as "[HeTr' HeTr'']". *)
Require Import Dot.tactics.
      cbn [is_syn_tm is_syn_ty] in * |- ; ev.
      iMod (ex_t_tm [] (length Γ) e1) as (e1') "#He1Tr"; first done.
      iMod (ex_t_vl [] (length Γ) v2) as (v2') "#Hv2Tr"; first done.
      assert (is_syn_ty (S (length Γ)) T2) by admit.
      iMod (ex_t_ty [] (S (length Γ)) T2) as (T2') "#HTTr"; first done.
      (* Here we seem to need a substitution lemma for the translation of types! *)
      assert (t_ty [] T2.|[v2/] T2'.|[v2'/]) by admit.
      iExists Γ, (tapp e1' (tv v2')), T2'.|[v2'/].
      repeat iSplitL; try done.
      + iApply H3.
      +
        (* XXX: Here, recursive calls to the lemma still produce a fresh translation,
           not the one we have; since translation isn't deterministic, that's bad.
           We should take translations as hypotheses. *)
      iMod (not_yet_fundamental Γ e1 _ HT1) as (Γ' e1'' T0') "#(H1 & H2 & H3)".
      iMod (not_yet_fundamental Γ (tv v2) _ HT2) as (Γ'' e2'' T0'') "#(H4 & H5 & H6)".

      (* iEval (cbn [t_tm]) in "HeTr". progress (case_match; try done); subst; *)
      (* repeat iMatchHyp (fun H P => match P with *)
      (*                       | (_ ∧ _)%I => *)
      (*                         iDestruct H as "[#HA #HB]" *)
      (*                       end). *)
      (* fold (t_tm [] e1 t1). *)
      (* fold (t_tm [] (tv v2) t2). *)
      (* assert (e1'' = t2) as -> by admit. *)
      (* (* iEval (cbn) in "HB". progress (case_match; try done); subst. *) *)
      (* (* progress fold (t_vl [] v2 v). *) *)
      (* iClear "H4". *)
      (* iEval (cbn) in "H2". progress (case_match; try done); subst. *)
      (* iDestruct "H2" as "[H7 H8]". *)
      (* assert (e1' = t1) as -> by admit. *)
      (* assert (T0'' = t3) as -> by admit. *)
      (* assert (Γ'' = Γ') as -> by admit. *)
      (* (* progress fold (t_vl [] v2 v0). *) *)
      (* (* progress fold (t_tm [] e1 t1). *) *)
      (* iModIntro. *)
      (* (* iEval (simpl) in "HA". *) *)
      (* (* iSimpl in "HA". *) *)
  Admitted.

End fundamental.
