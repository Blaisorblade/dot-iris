From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import tactics.
Require Import Dot.unary_lr.
Require Import Dot.typing.
Require Import Dot.AAsynToSem.
Require Import Dot.tactics.
Require Import Dot.lr_lemma.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

(* Should use fresh names. *)
Ltac iDestrConjs :=
  iMatchHyp (fun H P => match P with
                        | (_ ∧ _)%I =>
                          iDestruct H as "[#HA #HB]"
                        end).

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
    is_syn_tm e.
  Admitted.

  Lemma typed_ty_is_syn Γ e T:
    Γ ⊢ₜ e : T →
    is_syn_ty T.
  Admitted.

  (* Check all types are syntactic. The number of free varibles changes. Probably drop free variable count from is_syn_*. *)
  Definition is_syn_ctx Γ := Forall is_syn_ty Γ.

  Lemma typed_ctx_is_syn Γ e T:
    Γ ⊢ₜ e : T →
    is_syn_ctx Γ.
  Admitted.

  Lemma translations_types_equivalent_vals T T' T'' v ρ:
    (t_ty T T' → t_ty T T'' → ⟦ T' ⟧ρ  v → ⟦ T'' ⟧ ρ v )%I.
  Proof. 
  Admitted.

  Lemma translations_types_equivalent e T T' T'' Γ:
    (t_ty T T' → t_ty T T'' → Γ ⊨ e : T' → Γ ⊨ e : T'' )%I.
  Proof. 
    iIntros "#A #B #C". iIntros (ρ). iModIntro. iIntros "#D".
    unfold interp_expr. simpl.
    iApply (wp_strong_mono); try done.
      { by iApply "C". }
    iIntros (v) "HT'". iModIntro. by iApply (translations_types_equivalent_vals T T' T'').
  Qed.

  Fixpoint not_yet_fundamental Γ e T e' T' (HT: Γ ⊢ₜ e : T) {struct HT}:
  (* Lemma not_yet_fundamental Γ e T e' T' (HT: Γ ⊢ₜ e : T): *)
    (t_tm e e' → t_ty T T' → |==> Γ ⊨ e' : T')%I.
  Proof.
    iIntros "#HtrE #HtrT".
    (* destruct HT. *)
     iInduction HT as [] "IHT" forall (e' T') "HtrE HtrT".
    -
      (* I'm careful with simplification to avoid unfolding too much. *)
      set (e2 := tv v2).
      cbn [t_tm] in * |- *; case_match; try done.
      iDestruct "HtrE" as "[Htr1 Htr2]".
      unfold e2.
      iEval (cbn [t_tm]) in "Htr2"; case_match; try done; fold (t_vl v2 v).
      iAssert (t_tm (tv v2) (tv v)) as "#Ht2"; first done.
      iMod (ex_t_ty (length Γ) T1) as (T1') "#HTT1r".
      (* fv_n: *) admit.
      { eauto using typed_ty_is_syn. }
      iMod (ex_t_ty (S (length Γ)) T2) as (T2') "#HTT2r".
      (* fv_n: *) admit.
      { assert (is_syn_ty (TAll T1 T2)) by eauto using typed_ty_is_syn. simpl in H0. intuition. }

      iPoseProof (not_yet_fundamental Γ e1 _ _ _ HT1 with "Htr1") as "HsT1".
      iMod (not_yet_fundamental Γ (tv v2) _ _ _ HT2 with "Ht2 HTT1r") as "#HsT2".
      iPoseProof ("IHT" $! t1 (TAll T1' T2') with "Htr1 []") as "toto".
      { iModIntro. unfold t_ty; simpl. fold t_ty. iSplit; try done. }
      iPoseProof ("IHT1" $! (tv v) T1' with "Ht2 []") as "tata".
      { iModIntro. unfold t_ty; simpl. fold t_ty. done. }
      iMod "toto". iMod "tata".

      iAssert (t_ty (T2.|[v2/]) (T2'.|[v/])) as "#HHH".
      { admit. }
      iApply (translations_types_equivalent); try done.

      by iApply (T_Forall_Ex  with "toto tata").
    - 
      (* I'm careful with simplification to avoid unfolding too much. *)
      cbn [t_tm] in * |- *; case_match; try done.
      iDestruct "HtrE" as "[Htr1 Htr2]".
      iMod (ex_t_ty (length Γ) T1) as (T1') "#HTTr".
      (* fv_n: *) admit.
      eauto using typed_ty_is_syn.
      iAssert (t_ty T2.|[ren (+1)] T'.|[ren (+1)]) as "#HtrT2s". { admit. }
      iAssert (t_ty (TAll T1 T2.|[ren (+1)]) (TAll T1' T'.|[ren (+1)])) as "#HtrTAll".
      { cbn; by iSplit. }
      iMod (not_yet_fundamental Γ e1 _ _ _ HT1 with "Htr1 HtrTAll") as "#HsT1".
      iMod (not_yet_fundamental Γ e2 _ _ _ HT2 with "Htr2 HTTr") as "#HsT2".
      by iApply (T_Forall_E with "HsT1 HsT2").

    (* pose proof (typed_tm_is_syn Γ e T HT) as HeSyn. *)
    (* pose proof (typed_ty_is_syn Γ e T HT) as HTSyn. *)
    (* pose proof (typed_ctx_is_syn Γ e T HT) as HΓSyn. *)

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
    (* iDestruct HT as ([]) "". "IHT" forall "HeTr HTTr". *)
    (* - *)
    (*   (* Arguments t_tm _ _ _ /. *) *)
    (*   (* Arguments t_vl _ _ _ /. *) *)

    (*   (* destruct e'; cbn [t_tm]; try done. *) *)
    (*   (* fold (t_tm [] e1 e'1). *) *)
    (*   (* fold (t_tm [] (tv v2) e'2). *) *)
    (*   (* iDestruct "HeTr" as "[HeTr' HeTr'']". *) *)
    (*   cbn [t_tm] in * |- *; case_match; iStartProof. *)
    (*   iMod (ex_t_tm [] (length Γ) e1) as (e1') "#He1Tr"; first done. *)
    (*   iMod (ex_t_vl [] (length Γ) v2) as (v2') "#Hv2Tr"; first done. *)
    (*   assert (is_syn_ty (S (length Γ)) T2) by admit. *)
    (*   iMod (ex_t_ty [] (S (length Γ)) T2) as (T2') "#HTTr"; first done. *)
    (*   (* Here we seem to need a substitution lemma for the translation of types! *) *)
    (*   assert (t_ty [] T2.|[v2/] T2'.|[v2'/]) by admit. *)
    (*   iExists Γ. (tapp e1' (tv v2')), T2'.|[v2'/]. *)
    (*   repeat iSplitL; try done. *)
    (*   + iApply H3. *)
    (*   + *)
    (*     (* XXX: Here, recursive calls to the lemma still produce a fresh translation, *)
    (*        not the one we have; since translation isn't deterministic, that's bad. *)
    (*        We should take translations as hypotheses. *) *)
    (*   iMod (not_yet_fundamental Γ e1 _ HT1) as (Γ' e1'' T0') "#(H1 & H2 & H3)". *)
    (*   iMod (not_yet_fundamental Γ (tv v2) _ HT2) as (Γ'' e2'' T0'') "#(H4 & H5 & H6)". *)

    (*   (* iEval (cbn [t_tm]) in "HeTr". progress (case_match; try done); subst; *) *)
    (*   (* repeat iMatchHyp (fun H P => match P with *) *)
    (*   (*                       | (_ ∧ _)%I => *) *)
    (*   (*                         iDestruct H as "[#HA #HB]" *) *)
    (*   (*                       end). *) *)
    (*   (* fold (t_tm [] e1 t1). *) *)
    (*   (* fold (t_tm [] (tv v2) t2). *) *)
    (*   (* assert (e1'' = t2) as -> by admit. *) *)
    (*   (* (* iEval (cbn) in "HB". progress (case_match; try done); subst. *) *) *)
    (*   (* (* progress fold (t_vl [] v2 v). *) *) *)
    (*   (* iClear "H4". *) *)
    (*   (* iEval (cbn) in "H2". progress (case_match; try done); subst. *) *)
    (*   (* iDestruct "H2" as "[H7 H8]". *) *)
    (*   (* assert (e1' = t1) as -> by admit. *) *)
    (*   (* assert (T0'' = t3) as -> by admit. *) *)
    (*   (* assert (Γ'' = Γ') as -> by admit. *) *)
    (*   (* (* progress fold (t_vl [] v2 v0). *) *) *)
    (*   (* (* progress fold (t_tm [] e1 t1). *) *) *)
    (*   (* iModIntro. *) *)
    (*   (* (* iEval (simpl) in "HA". *) *) *)
    (*   (* (* iSimpl in "HA". *) *) *)
  Admitted.

End fundamental.
