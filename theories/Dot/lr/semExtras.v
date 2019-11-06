From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr lr_lemmasDefs.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (p : path)
         (Γ : ctx).

Section Sec.
  Context `{HdlangG: dlangG Σ}.

  (** * When is a context weaker than another? *)
  (* Likely, this should be an iProp. *)
  Definition ctx_sub Γ1 Γ2 : Prop := ∀ ρ, ⟦ Γ1 ⟧* ρ -∗ ⟦ Γ2 ⟧* ρ.
  Infix "<:*" := ctx_sub (at level 70).

  (** * Basic lemmas about [ctx_sub]. *)
  (* TODO: Make this into a structural typing rule? *)

  (** Typing is contravariant in [Γ]. *)
  Lemma ietp_weaken_ctx {T e Γ1 Γ2} (Hweak : Γ1 <:* Γ2):
    Γ2 ⊨ e : T -∗ Γ1 ⊨ e : T.
  Proof. iIntros "#HT1 !>" (ρ) "#HG". iApply "HT1". by iApply Hweak. Qed.

  (** The strength ordering of contexts lifts the strength ordering of types. *)
  Lemma env_lift_sub f g {Γ} (Hweak: ∀ T ρ v, ⟦ f T ⟧ ρ v -∗ ⟦ g T ⟧ ρ v):
    f <$> Γ <:* g <$> Γ.
  Proof.
    elim: Γ => [//| T Γ IH] ρ. cbn; rewrite (Hweak T).
    iIntros "[HG $]". by iApply IH.
  Qed.

  Lemma env_lift_sub' f g Γ {Γ1 Γ2}:
    Γ1 = f <$> Γ → Γ2 = g <$> Γ →
    (∀ T ρ v, ⟦ f T ⟧ ρ v -∗ ⟦ g T ⟧ ρ v) →
    Γ1 <:* Γ2.
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
  Lemma TLater_ctx_sub Γ : Γ <:* TLater <$> Γ.
  Proof. apply (env_lift_sub' id TLater Γ); rewrite ?list_fmap_id; auto. Qed.

  Lemma TLater_unTLater_ctx_sub Γ : Γ <:* TLater <$> (unTLater <$> Γ).
  Proof.
    rewrite -list_fmap_compose.
    apply (env_lift_sub' id (TLater ∘ unTLater) Γ), TLater_unTLater_sub;
      by rewrite ?list_fmap_id.
  Qed.

  Lemma TLater_unTLater_TLater_ctx_sub Γ :
    TLater <$> (unTLater <$> Γ) <:* TLater <$> Γ.
  Proof.
    rewrite -list_fmap_compose.
    apply env_lift_sub, TLater_unTLater_sub_TLater.
  Qed.

  Lemma ctx_sub_unTLater Γ : unTLater <$> Γ <:* Γ.
  Proof.
    apply (env_lift_sub' unTLater id Γ), unTLater_sub;
      by rewrite ?list_fmap_id.
  Qed.

  (*XXX : move away from here. Avoid auto-dropping box (and unfolding) when introducing ietp persistently. *)
  Instance: IntoPersistent false (ietp Γ T e) (ietp Γ T e) | 0 := _.

  Lemma T_later_ctx Γ V T e:
    TLater <$> (V :: Γ) ⊨ e : T -∗
    (*─────────────────────────*)
    TLater V :: Γ ⊨ e : T.
  Proof. iApply ietp_weaken_ctx => ρ; cbn. by rewrite (TLater_ctx_sub Γ). Qed.

  Lemma env_TLater_commute Γ ρ : ⟦ TLater <$> Γ ⟧* ρ ⊣⊢ ▷ ⟦ Γ ⟧* ρ.
  Proof.
    elim: Γ ρ => [| T Γ IH] ρ; cbn; [|rewrite IH later_and];
      iSplit; by [iIntros "$" | iIntros "_"].
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

  Lemma T_Forall_I {Γ} T1 T2 e:
    T1.|[ren (+1)] :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "HeT"; iApply T_Forall_I_Strong;
      iApply (ietp_weaken_ctx with "HeT") => ρ.
    by rewrite /= ctx_sub_unTLater.
  Qed.

  Lemma T_Forall_I' {Γ} T1 T2 e:
    TLater T1.|[ren (+1)] :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "HeT"; iApply T_Forall_I;
      iApply (ietp_weaken_ctx with "HeT").
    iIntros (ρ) "[$ $]".
  Qed.

  Lemma T_Forall_I_strange {Γ} V T1 T2 e:
    T1.|[ren (+1)] :: V :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ |L V ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "HeT"; iApply T_Forall_I_Strong;
      iApply (ietp_weaken_ctx with "HeT") => ρ.
    by rewrite /= ctx_sub_unTLater.
  Qed.

  Lemma TVMem_All_I_derived {Γ} V T1 T2 e l:
    T1.|[ren (+1)] :: V :: Γ ⊨ e : T2 -∗
    Γ |L V ⊨ { l := dvl (vabs e) } : TVMem l (TAll T1 T2).
  Proof.
    iIntros "HeT"; iApply TVMem_I.
    iApply (T_Forall_I with "HeT").
  Qed.
End Sec.
