From iris.proofmode Require Import tactics.
From D Require Import tactics.
From D.Dot Require Import unary_lr unary_lr_binding typing typeExtractionSem synLemmas.
From D.Dot Require Import lr_lemma lr_lemmasDefs lr_lemma_nobinding lr_lemmasTSel.

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
  (* (* XXX lift translation and is_syn to contexts. Show that syntactic typing *)
  (*    implies is_syn and closure. Stop talking about free variables inside is_syn? *) *)
  (* Lemma typed_tm_is_syn Γ e T: *)
  (*   Γ ⊢ₜ e : T → *)
  (*   is_syn_tm e. *)
  (* Admitted. *)

  (* Lemma typed_ty_is_syn Γ e T: *)
  (*   Γ ⊢ₜ e : T → *)
  (*   is_syn_ty T. *)
  (* Admitted. *)

  (* (* Check all types are syntactic. *) *)
  (* Definition is_syn_ctx Γ := Forall is_syn_ty Γ. *)

  (* Lemma typed_ctx_is_syn Γ e T: *)
  (*   Γ ⊢ₜ e : T → *)
  (*   is_syn_ctx Γ. *)
  (* Admitted. *)

  Lemma wp_and (P1 P2: vl → iProp Σ) e:
    ((WP e {{ P1 }} ) -∗ (WP e  {{ P2 }} ) -∗ WP e {{ v, P1 v ∧ P2 v }})%I.
  Proof.
    iLöb as "IH" forall (e).
    iIntros "H1 H2".
    iEval (rewrite !wp_unfold /wp_pre) in "H1";
    iEval (rewrite !wp_unfold /wp_pre) in "H2";
    iEval (rewrite !wp_unfold /wp_pre).
    case_match. auto.
    iIntros (σ1 k ks n) "#Ha".
    iDestruct ("H1" $! σ1 k ks n with "Ha") as "[$ H1]".
    iDestruct ("H2" $! σ1 k ks n with "Ha") as "[% H2]".
    iIntros (e2 σ2 efs Hstep).
    iSpecialize ("H1" $! e2 σ2 efs Hstep);
    iSpecialize ("H2" $! e2 σ2 efs Hstep).
    iNext.
    iDestruct "H1" as "[$ [H1 $]]".
    iDestruct "H2" as "[_ [H2 _]]".
    iApply ("IH" with "H1 H2").
  Qed.

  (* XXX these statements point out we need to realign the typing judgemnts. *)
  (* XXX *)
  Lemma fundamental_dm_typed Γ V d T (HT: Γ |d V ⊢ d : T):
    wellMapped getStampTable -∗ TLater V :: Γ ⊨d d : T.
  Proof.
    iIntros "#Hm"; iInduction HT as [] "IHT".
    -
      (* XXX Cheat for simplicity, since the semantic typing lemma makes
        more assumptions on σ than it should. *)
      have ?: σ = idsσ (length (TLater V :: Γ)). admit. subst.
      (* Remaining admits are fixable by making all these lemmas mutually recursive. *)
      iApply (@idtp_tmem_abs_i _ _ _ T). admit. admit.
      (** If g is well mapped and it maps syntactically s to T,
          then s also maps semantically to ⟦ T ⟧. Specialized proof: *)
      cbn in *.
      destruct H as (T' & Heq & HT'T & Hclσ & HclT).
      iSpecialize ("Hm" $! s T' Heq).
      iDestruct "Hm" as (φ) "[Hm1 %]". move: H => HT'φ.
      iDestruct "Hm1" as (γ) "[Hsγ Hγ]".
      iExists γ. iFrame "Hsγ".
      rewrite (closed_subst_idsρ T' (S (length Γ))) in HT'T.
      rewrite -HT'T -HT'φ //.
      rewrite length_idsσr // in HclT.
    - iApply idtp_vmem_i. admit.
  Admitted.

  Lemma fundamental_dms_typed Γ V ds T (HT: Γ |ds V ⊢ ds : T):
    wellMapped getStampTable -∗ TLater V :: Γ ⊨ds ds : T.
  Admitted.
  (* XXX *)
  Lemma fundamental_subtype Γ T1 i1 T2 i2 (HT: Γ ⊢ₜ T1, i1 <: T2, i2):
    wellMapped getStampTable -∗ Γ ⊨ [T1, i1] <: [T2, i2].
  Admitted.

  Lemma TAnd_I Γ e T1 T2:
    Γ ⊨ e : T1 -∗
    Γ ⊨ e : T2 -∗
    Γ ⊨ e : TAnd T1 T2.
  Proof.
    iIntros "#HT #HT1". cbn.
    (* iDestruct "HT" as "[% #HT]". *) (* Works *)
    (* Fail iDestruct "HT" as "[$ #HT]". *)
    iDestruct "HT" as "[$ #HT']". iClear "HT".
    iDestruct "HT1" as (_) "#HT1".
    iIntros "!>" (ρ) "#Hg".
    iSpecialize ("HT'" with "Hg").
    iSpecialize ("HT1" with "Hg").
    by iApply wp_and.
  Qed.

  Lemma fundamental_typed Γ e T (HT: Γ ⊢ₜ e : T):
    wellMapped getStampTable -∗ Γ ⊨ e : T.
  Proof.
    iIntros "#Hm"; iInduction HT as [] "IHT".
    - by iApply T_Forall_Ex.
    - by iApply T_Forall_E.
    - by iApply T_Mem_E.
    - by iApply TMu_E.
    - by iApply T_Forall_I.
    - iApply T_New_I.
      by iApply fundamental_dms_typed.
    - by iApply TMu_I.
    - by iApply T_Nat_I.
    - by iApply T_Var.
    - iApply T_Sub => //.
      by iApply fundamental_subtype.
    - by iApply TAnd_I.
  Qed.

  Lemma fundamental_typed_upd Γ e T (HT: Γ ⊢ₜ e : T): (allGs ∅ -∗ |==> Γ ⊨ e : T)%I.
  Proof.
    iIntros.
    iApply fundamental_typed => //.
    iApply transfer; last eauto; eauto.
  Qed.

End fundamental.
