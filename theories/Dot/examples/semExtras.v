From iris.proofmode Require Import tactics.
From D Require Import swap_later_impl.
From D.Dot Require Import unary_lr lr_lemmasDefs.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (p : path)
         (Γ : ctx).

Section Sec.
  Context `{HdlangG: dlangG Σ}.

  Definition unTLater T : ty := match T with TLater T' => T' | _ => T end.
  Lemma unTLater_to T ρ v : ⟦ unTLater T ⟧ ρ v -∗ ⟦ T ⟧ ρ v.
  Proof. case: T => //= T. by auto. Qed.
  Lemma TLater_unTLater_to T ρ v : ⟦ T ⟧ ρ v -∗ ⟦ TLater (unTLater T) ⟧ ρ v.
  Proof. destruct T; iIntros "$". Qed.

  Lemma TLater_unTLater_to_TLater T ρ v :
    ⟦ TLater (unTLater T) ⟧ ρ v -∗ ⟦ TLater T ⟧ ρ v.
  Proof. destruct T; iIntros "$". Qed.

  Lemma map_env f g Γ ρ (Hweak : (∀ T ρ v, ⟦ f T ⟧ ρ v -∗ ⟦ g T ⟧ ρ v)):
    ⟦ f <$> Γ ⟧* ρ -∗ ⟦ g <$> Γ ⟧* ρ.
  Proof.
    elim: Γ ρ => [//| T Γ IH] ρ; cbn. rewrite (Hweak T).
    iIntros "[HG $]". by iApply IH.
  Qed.

  Lemma env_map_TLater Γ ρ : ⟦ Γ ⟧* ρ -∗ ⟦ TLater <$> Γ ⟧* ρ.
  Proof. rewrite -{1}(list_fmap_id Γ); apply map_env => /=. auto. Qed.

  Lemma env_map_TLater_unTLater Γ ρ :
    ⟦ Γ ⟧* ρ -∗ ⟦ TLater <$> (unTLater <$> Γ) ⟧* ρ.
  Proof.
    rewrite -{1}(list_fmap_id Γ) -list_fmap_compose; apply map_env.
    apply TLater_unTLater_to.
  Qed.

  Lemma env_map_TLater_unTLater_TLater Γ ρ :
    ⟦ TLater <$> (unTLater <$> Γ) ⟧* ρ -∗ ⟦ TLater <$> Γ ⟧* ρ.
  Proof.
    rewrite -list_fmap_compose; apply (map_env (TLater ∘ unTLater) TLater).
    apply TLater_unTLater_to_TLater.
  Qed.

  Lemma map_unTLater_env Γ ρ : ⟦ unTLater <$> Γ ⟧* ρ -∗ ⟦ Γ ⟧* ρ.
  Proof.
    rewrite -{2}(list_fmap_id Γ); apply map_env.
    apply unTLater_to.
  Qed.

  (* TODO: Make this into a structural typing rule? *)
  Lemma ietp_weaken_ctx {T e} Γ1 Γ2 (Hweak : ∀ ρ, ⟦ Γ2 ⟧* ρ -∗ ⟦ Γ1 ⟧* ρ):
    Γ1 ⊨ e : T -∗ Γ2 ⊨ e : T.
  Proof. iIntros "#HT1 !>" (ρ) "#HG". iApply "HT1". by iApply Hweak. Qed.

  Lemma T_later_unlater_ctx Γ T e:
    TLater <$> (unTLater <$> Γ) ⊨ e : T -∗
    (*─────────────────────────*)
    Γ ⊨ e : T.
  Proof. iApply ietp_weaken_ctx. apply env_map_TLater_unTLater. Qed.

  Lemma T_later_ctx_v1 Γ V T e:
    TLater <$> (V :: Γ) ⊨ e : T -∗
    (*─────────────────────────*)
    TLater V :: Γ ⊨ e : T.
  Proof. iApply ietp_weaken_ctx => ρ. by rewrite /= (env_map_TLater Γ). Qed.

  (*XXX : move away from here. Avoid auto-dropping box (and unfolding) when introducing ietp persistently. *)
  Instance: IntoPersistent false (ietp Γ T e) (ietp Γ T e) | 0 := _.

  Lemma T_later_ctx_v2 Γ V T e:
    TLater <$> (V :: Γ) ⊨ e : T -∗
    (*─────────────────────────*)
    TLater V :: Γ ⊨ e : T.
  Proof.
    (* iIntros "#HeT". iApply T_later_unlater_ctx.
    iApply (ietp_weaken_ctx with "HeT") => ρ.
    by rewrite /= (env_map_TLater_unTLater_TLater Γ).
    Restart. *)

    iApply ietp_weaken_ctx => ρ.
    (* cbn; rewrite (env_map_TLater Γ). *)
    rewrite (env_map_TLater_unTLater (_ :: Γ)).
    by cbn; rewrite (env_map_TLater_unTLater_TLater Γ).
  Qed.

  (* Lemma map_unTLater_env_strong Γ ρ : ⟦ unTLater <$> Γ ⟧* ρ ⊢ ▷ ⟦ Γ ⟧* ρ.
  Proof.
    elim: Γ ρ => [| T Γ IH] ρ. by auto.
    cbn; rewrite IH unTLater_to. iIntros "[$ $]".
  Qed. *)
  Lemma map_unTLater_env_strong_v2 Γ ρ : ⟦ Γ ⟧* ρ ⊢ ▷ ⟦ unTLater <$> Γ ⟧* ρ.
  Proof.
    elim: Γ ρ => [| T Γ IH] ρ. by auto.
    cbn. rewrite IH TLater_unTLater_to. iIntros "[$ $]".
  Qed.

  Lemma T_Forall_I_Good {Γ} T1 T2 e:
    T1.|[ren (+1)] :: (unTLater <$> Γ) ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "#HeT !>" (ρ) "#HG /=".
    rewrite -wp_value'. iExists _; iSplit; first done.
    iIntros "!>" (v); rewrite -(decomp_s _ (v .: ρ)).
    rewrite (map_unTLater_env_strong_v2 Γ).
    iIntros "!> #Hv".
    iApply ("HeT" $! (v .: ρ) with "[$HG]").
    by rewrite (interp_weaken_one T1 _ v) stail_eq.
  Qed.

  Context {Γ}.

  Lemma T_Forall_I_strange V T1 T2 e:
    T1.|[ren (+1)] :: V :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    TLater V :: Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "HeT".
    iApply T_Forall_I_Good.
    iApply (ietp_weaken_ctx with "HeT") => ρ.
    by rewrite /= map_unTLater_env.
  Qed.

  Lemma T_Forall_I' T1 T2 e:
    TLater T1.|[ren (+1)] :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "HeT".
    iApply T_Forall_I_Good.
    iApply (ietp_weaken_ctx with "HeT") => ρ.
    rewrite /= map_unTLater_env. iIntros "[$ $]".
  Qed.

  Lemma TVMem_Sub V T1 T2 v l:
    Γ |L V ⊨ { l := dvl v } : TVMem l T1 -∗
    Γ |L V ⊨ T1, 0 <: T2, 0 -∗
    Γ |L V ⊨ { l := dvl v } : TVMem l T2.
  Proof.
    iIntros "/= #Hv #Hsub !>" (ρ) "#Hg"; iApply def_interp_tvmem_eq.
    iApply ("Hsub" with "Hg").
    iApply def_interp_tvmem_eq. by iApply "Hv".
  Qed.

  Lemma TVMem_All_I_derived V T1 T2 e l:
    T1.|[ren (+1)] :: V :: Γ ⊨ e : T2 -∗
    Γ |L V ⊨ { l := dvl (vabs e) } : TVMem l (TAll T1 T2).
  Proof.
    iIntros "He". iApply TVMem_I. iApply (T_Forall_I_strange with "He").
  Qed.

  Lemma TVMem_All_I' V T1 T2 e l L:
    T1.|[ren (+1)] :: V :: Γ ⊨ e : T2 -∗
    TLater V :: Γ ⊨ TAll T1 T2, 0 <: L, 0 -∗
    Γ |L V ⊨ { l := dvl (vabs e) } : TVMem l L.
  Proof.
    iIntros "He Hsub".
    iApply (TVMem_Sub with "[He] Hsub").
    iApply TVMem_I.
    iApply (T_Forall_I_strange with "He").
  Qed.

  Lemma wp_later_swap t Φ: WP t {{ v, ▷ Φ v }} ⊢ ▷ WP t {{ v, Φ v }}.
  Proof.
    iLöb as "IH" forall (t Φ).
    iEval (rewrite !wp_unfold /wp_pre /=).
    case: (to_val t) => [v|]. by eauto.
    iIntros "H" (σ1 κ κs n _); iDestruct ("H" $! σ1 κ κs n with "[#//]") as "[$ H]".
    iIntros (e2 σ2 efs Hstep); iDestruct ("H" $! e2 σ2 efs Hstep) as "[$ [H $]]".
    iApply ("IH" with "H").
  Qed.

  Lemma T_Forall_I'' T1 T2 e `{SwapPropI Σ}:
    TLater T1.|[ren (+1)] :: Γ ⊨ e : TLater T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "/= #HeT !>" (vs) "#HG".
    rewrite -wp_value'. iExists _; iSplitL; first done.
    iIntros "!>" (v); rewrite -(decomp_s e (v .: vs)).
    rewrite -wand_later; iIntros "#Hv".
    (* iApply (wp_later_swap _ (⟦ T2 ⟧ (v .: vs))).
    iApply ("HeT" $! (v .: vs) with "[$HG]"). *)
    iSpecialize ("HeT" $! (v .: vs) with "[$HG]").
    by rewrite (interp_weaken_one T1 _ v).
    iApply (wp_later_swap with "HeT").
  Qed.

  (** Stronger version of TAll_Later_Swap0, needs wp_later_swap, which
      might not extend to to WPs?*)
  Lemma TAll_Later_Swap `{SwapPropI Σ} T U i:
    Γ ⊨ TAll (TLater T) (TLater U), i <: TLater (TAll T U), i.
  Proof.
    iIntros "!>" (ρ v) "_ /= #HvTU". iNext i.
    iDestruct "HvTU" as (t ->) "#HvTU".
    iExists t; iSplit => //.
    iNext.
    iIntros (w); rewrite -mlater_wand; iIntros "!> #HwT".
    rewrite -(wp_later_swap _ (⟦ _ ⟧ _)).
    iApply (wp_wand with "(HvTU [# $HwT //])").
    by iIntros (v) "$".
  Qed.
End Sec.
