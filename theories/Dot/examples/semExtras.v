From iris.proofmode Require Import tactics.
From D Require Import swap_later_impl.
From D.Dot Require Import unary_lr lr_lemmasDefs.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (p : path)
         (Γ : ctx).

Section Sec.
  Context `{HdlangG: dlangG Σ}.

  (** * When is a context weaker than another? *)
  (* Likely, this should be an iProp. *)
  Definition ctx_sub Γ1 Γ2 : Prop := ∀ ρ, ⟦ Γ2 ⟧* ρ -∗ ⟦ Γ1 ⟧* ρ.

  (** * Basic lemmas about [ctx_sub]. *)
  (* TODO: Make this into a structural typing rule? *)

  (** Typing is contravariant in [Γ]. *)
  Lemma ietp_weaken_ctx {T e} Γ1 Γ2 (Hweak : ctx_sub Γ1 Γ2):
    Γ1 ⊨ e : T -∗ Γ2 ⊨ e : T.
  Proof. iIntros "#HT1 !>" (ρ) "#HG". iApply "HT1". by iApply Hweak. Qed.

  (** The strength ordering of contexts lifts the strength ordering of types. *)
  Lemma env_lift_sub f g {Γ} (Hweak: ∀ T ρ v, ⟦ f T ⟧ ρ v -∗ ⟦ g T ⟧ ρ v):
    ctx_sub (g <$> Γ) (f <$> Γ).
  Proof.
    elim: Γ => [//| T Γ IH] ρ. cbn; rewrite (Hweak T).
    iIntros "[HG $]". by iApply IH.
  Qed.

  Lemma env_lift_sub' f g Γ {Γ1 Γ2}:
    Γ1 = g <$> Γ → Γ2 = f <$> Γ →
    (∀ T ρ v, ⟦ f T ⟧ ρ v -∗ ⟦ g T ⟧ ρ v) →
    ctx_sub Γ1 Γ2.
  Proof. move => -> -> Hweak. exact: env_lift_sub. Qed.

  (** A left inverse of TLater. Sometimes written ⊲. *)
  Definition unTLater T : ty := match T with TLater T' => T' | _ => T end.

  Definition unTLater_TLater T: unTLater (TLater T) = T := reflexivity _.
  Global Instance: Cancel (=) unTLater TLater. Proof. exact: unTLater_TLater. Qed.

  (** Ordering of logical strength:
      unTLater T <: T <: TLater (unTLater T) <: TLater T. *)

  Lemma unTLater_sub T ρ v : ⟦ unTLater T ⟧ ρ v -∗ ⟦ T ⟧ ρ v.
  Proof. case: T => //= T. by auto. Qed.

  Lemma TLater_unTLater_sub T ρ v : ⟦ T ⟧ ρ v -∗ ⟦ TLater (unTLater T) ⟧ ρ v.
  Proof. destruct T; iIntros "$". Qed.

  Lemma TLater_unTLater_sub_TLater T ρ v :
    ⟦ TLater (unTLater T) ⟧ ρ v -∗ ⟦ TLater T ⟧ ρ v.
  Proof. destruct T; iIntros "$". Qed.

  (** Lift the above ordering to environments. *)
  Lemma TLater_ctx_sub Γ : ctx_sub (TLater <$> Γ) Γ.
  Proof. apply (env_lift_sub' id TLater Γ); rewrite ?list_fmap_id; auto. Qed.

  Lemma TLater_unTLater_ctx_sub Γ : ctx_sub (TLater <$> (unTLater <$> Γ)) Γ.
  Proof.
    rewrite -list_fmap_compose.
    apply (env_lift_sub' id (TLater ∘ unTLater) Γ), TLater_unTLater_sub;
      by rewrite ?list_fmap_id.
  Qed.

  Lemma TLater_unTLater_TLater_ctx_sub Γ :
    ctx_sub (TLater <$> Γ) (TLater <$> (unTLater <$> Γ)).
  Proof.
    rewrite -list_fmap_compose.
    apply env_lift_sub, TLater_unTLater_sub_TLater.
  Qed.

  Lemma ctx_sub_unTLater Γ : ctx_sub Γ (unTLater <$> Γ).
  Proof.
    apply (env_lift_sub' unTLater id Γ), unTLater_sub;
      by rewrite ?list_fmap_id.
  Qed.

  (* Lemma T_later_unlater_ctx Γ T e:
    TLater <$> (unTLater <$> Γ) ⊨ e : T -∗
    (*─────────────────────────*)
    Γ ⊨ e : T.
  Proof. iApply ietp_weaken_ctx. apply TLater_unTLater_ctx_sub. Qed. *)

  (* Lemma T_later_ctx_v1 Γ V T e:
    TLater <$> (V :: Γ) ⊨ e : T -∗
    (*─────────────────────────*)
    TLater V :: Γ ⊨ e : T.
  Proof. iApply ietp_weaken_ctx => ρ. by rewrite /= (TLater_ctx_sub Γ). Qed. *)

  (*XXX : move away from here. Avoid auto-dropping box (and unfolding) when introducing ietp persistently. *)
  Instance: IntoPersistent false (ietp Γ T e) (ietp Γ T e) | 0 := _.

  Lemma T_later_ctx_v2 Γ V T e:
    TLater <$> (V :: Γ) ⊨ e : T -∗
    (*─────────────────────────*)
    TLater V :: Γ ⊨ e : T.
  Proof. iApply ietp_weaken_ctx => ρ; cbn. by rewrite (TLater_ctx_sub Γ). Qed.

  (* Lemma ctx_sub_unTLater_strong Γ ρ : ⟦ unTLater <$> Γ ⟧* ρ ⊢ ▷ ⟦ Γ ⟧* ρ.
  Proof.
    elim: Γ ρ => [| T Γ IH] ρ. by auto.
    cbn; rewrite IH unTLater_sub. iIntros "[$ $]".
  Qed. *)
  Lemma env_TLater_commute Γ ρ : ⟦ TLater <$> Γ ⟧* ρ ⊢ ▷ ⟦ Γ ⟧* ρ.
  Proof.
    elim: Γ ρ => [| T Γ IH] ρ; cbn. by auto.
    rewrite IH later_and; iIntros "$".
  Qed.

  Lemma T_Forall_I_Strong {Γ} T1 T2 e:
    T1.|[ren (+1)] :: (unTLater <$> Γ) ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "#HeT !>" (ρ) "#HG /=".
    rewrite -wp_value'. iExists _; iSplit; first done.
    iIntros "!>" (v); rewrite -(decomp_s _ (v .: ρ)).
    (* Factor ⪭ out of [⟦ Γ ⟧* ρ] before [iNext]. *)
    rewrite TLater_unTLater_ctx_sub env_TLater_commute. iNext.
    iIntros "#Hv".
    iApply ("HeT" $! (v .: ρ) with "[$HG]").
    by rewrite (interp_weaken_one T1 _ v) stail_eq.
  Qed.

  Context {Γ}.

  Lemma T_Forall_I_strange V T1 T2 e:
    T1.|[ren (+1)] :: V :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    TLater V :: Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "HeT". iApply T_Forall_I_Strong.
    iApply (ietp_weaken_ctx with "HeT") => ρ.
    by rewrite /= ctx_sub_unTLater.
  Qed.

  Lemma T_Forall_I' T1 T2 e:
    TLater T1.|[ren (+1)] :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "HeT".
    iApply T_Forall_I_Strong.
    iApply (ietp_weaken_ctx with "HeT") => ρ.
    rewrite /= ctx_sub_unTLater. iIntros "[$ $]".
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
    by iApply TVMem_All_I_derived.
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
