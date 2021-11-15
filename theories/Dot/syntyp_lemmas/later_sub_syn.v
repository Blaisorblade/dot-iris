(** * When is a context weaker than another? Semantic version. *)


From D Require Import proper.
From D.Dot Require Import later_sub_sem.
From D.Dot Require Import unary_lr.
From D.Dot Require Import typing_aux_defs.
From D.Dot Require Import type_eq.
From D.Dot Require Import dsub_lr. (* XXX *)

Set Suggest Proof Using.
Set Default Proof Using "Type".

Section TypeEquiv.
  Context `{HdlangG : !dlangG Σ}.

  Lemma fundamental_mut_equiv_clty :
    (∀ T1 T2 (H : |- T1 == T2), C⟦ T1 ⟧ ≡ C⟦ T2 ⟧) ∧
    (∀ K1 K2 (H : |-K K1 == K2), K⟦ K1 ⟧ ≡ K⟦ K2 ⟧).
  Proof.
    apply: type_kind_eq_mut_ind;
      cbn; rewrite /pty_interp; intros.
    by rewrite cAnd_olty2clty sTEq_oLaterN_oAnd.
    by rewrite sTEq_oLaterN_oOr.
    all: try reflexivity.
    all: repeat no_eq_f_equiv.
    all: try solve [assumption|symmetry; assumption].
    by etrans.
    by etrans.
  Qed.

  Lemma fundamental_type_equiv_clty T1 T2 (H : |- T1 == T2) :
    C⟦ T1 ⟧ ≡ C⟦ T2 ⟧.
  Proof. by apply fundamental_mut_equiv_clty. Qed.
  Lemma fundamental_kind_equiv_clty K1 K2 (H : |-K K1 == K2) :
    K⟦ K1 ⟧ ≡ K⟦ K2 ⟧.
  Proof. by apply fundamental_mut_equiv_clty. Qed.

  Lemma fundamental_type_equiv_olty T1 T2 :
    |- T1 == T2 → V⟦ T1 ⟧ ≡ V⟦ T2 ⟧.
  Proof. apply fundamental_type_equiv_clty. Qed.

  Lemma idstp_respects_type_equiv Γ ds T1 T2 (Heq : |- T1 == T2) :
    Γ ⊨ds ds : T1 -∗ Γ ⊨ds ds : T2.
  Proof. by apply equiv_entails, sdstp_proper, fundamental_type_equiv_clty. Qed.

  Lemma ietp_respects_type_equiv Γ e T1 T2 (Heq : |- T1 == T2) :
    Γ ⊨ e : T1 -∗ Γ ⊨ e : T2.
  Proof. by apply equiv_entails, setp_proper, fundamental_type_equiv_olty. Qed.

  Lemma ietp_teq_proper Γ : Proper (type_equiv ==> (=) ==> (⊢)) (ietp Γ).
  Proof. repeat intro; subst. exact: ietp_respects_type_equiv. Qed.

  (* XXX All these instances are local, because setoid rewriting doesn't work
  for some reason, but I don't feel like debugging it. *)
  Instance istpd_teq_proper Γ i :
    Proper (type_equiv ==> type_equiv ==> (⊣⊢)) (istpd i Γ).
  Proof.
    by repeat intro; apply sstpd_proper; [|
      exact: fundamental_type_equiv_olty..].
  Qed.

  #[global] Instance : Params (@istpd) 4 := {}.

  Lemma Stp_Eq i T1 T2 Γ :
    |- T1 == T2 → ⊢ Γ ⊨ T1 <:[i] T2.
  Proof.
    intros Heq.
    iApply istpd_teq_proper; [eassumption|reflexivity|iApply sStp_Refl].
  Qed.
End TypeEquiv.

Definition ty_sub `{HdlangG : !dlangG Σ} T1 T2 := s⊨T V⟦ T1 ⟧ <: V⟦ T2 ⟧.
Notation "⊨T T1 <: T2" := (ty_sub T1 T2) (at level 74, T1, T2 at next level).

Definition ctx_sub `{HdlangG : !dlangG Σ} Γ1 Γ2 : Prop := s⊨G V⟦ Γ1 ⟧* <:* V⟦ Γ2 ⟧*.
Notation "⊨G Γ1 <:* Γ2" := (ctx_sub Γ1 Γ2) (at level 74, Γ1, Γ2 at next level).

Section CtxSub.
  Context `{HdlangG : !dlangG Σ}.
  Implicit Type (T : ty) (Γ : ctx).

  (** * Basic lemmas about [ctx_sub]. *)
  #[global] Instance : RewriteRelation ty_sub := {}.
  #[global] Instance : PreOrder ty_sub.
  Proof. rewrite /ty_sub; split; first done. by move => x y z H1 H2; etrans. Qed.

  #[global] Instance : RewriteRelation ctx_sub := {}.
  #[global] Instance : PreOrder ctx_sub.
  Proof. rewrite /ctx_sub; split; first done. by move => x y z H1 H2; etrans. Qed.

  #[global] Instance cons_ctx_sub_mono : Proper (ty_sub ==> ctx_sub ==> ctx_sub) cons.
  Proof. rewrite /ty_sub /ctx_sub. solve_proper. Qed.
  #[global] Instance cons_ctx_sub_flip_mono : Proper (flip ty_sub ==> flip ctx_sub ==> flip ctx_sub) cons.
  Proof. solve_proper. Qed.

  #[global] Instance ietp_mono : Proper (flip ctx_sub ==> (=) ==> (=) ==> (⊢)) ietp.
  Proof.
    rewrite /ctx_sub /flip /ietp => Γ1 Γ2 Hweak ??????; subst. by rewrite Hweak.
  Qed.

  #[global] Instance ietp_flip_mono :
    Proper (ctx_sub ==> flip (=) ==> flip (=) ==> flip (⊢)) ietp.
  Proof. apply: flip_proper_4. Qed.

  #[global] Instance istpd_mono i :
    Proper (flip ctx_sub ==> (=) ==> (=) ==> (⊢)) (istpd i).
  Proof.
    rewrite /ctx_sub /flip /istpd => Γ1 Γ2 Hweak ??????; subst.
    by rewrite Hweak.
  Qed.
  #[global] Instance istpi_flip_mono i :
    Proper (ctx_sub ==> flip (=) ==> flip (=) ==> flip (⊢)) (istpd i).
  Proof. apply: flip_proper_4. Qed.

  #[global] Instance TLater_mono : Proper (ty_sub ==> ty_sub) TLater.
  Proof. by rewrite /ty_sub => ?? /= ->. Qed.
  #[global] Instance TLater_flip_mono :
    Proper (flip ty_sub ==> flip ty_sub) TLater.
  Proof. apply: flip_proper_2. Qed.

  Lemma fmap_TLater_oLater Γ : V⟦ TLater <$> Γ ⟧* = oLater <$> V⟦ Γ ⟧*.
  Proof. elim: Γ => [//| T Γ IH]; cbn. by rewrite IH. Qed.

  Lemma env_TLater_commute Γ ρ : G⟦ TLater <$> Γ ⟧ ρ ⊣⊢ ▷ G⟦ Γ ⟧ ρ.
  Proof. by rewrite -senv_TLater_commute fmap_TLater_oLater. Qed.

  (** The strength ordering of contexts lifts the strength ordering of types. *)
  Lemma env_lift_sub f g {Γ} (Hle : ∀ T, ⊨T f T <: g T) :
    ⊨G f <$> Γ <:* g <$> Γ.
  Proof. elim: Γ => [//| T Γ IH] ρ; cbn. by rewrite (Hle T _ _) -(IH _). Qed.

  Lemma env_lift_sub' f g Γ {Γ1 Γ2} :
    Γ1 = f <$> Γ → Γ2 = g <$> Γ →
    (∀ T, ⊨T f T <: g T) →
    ⊨G Γ1 <:* Γ2.
  Proof. move => -> -> Hweak. exact: env_lift_sub. Qed.

  (* It's not immediate to generalize fmap_TLater_proper to [fmap C] for a
  type constructor [C]. Fpr instance, the following is hopeless. *)
  (* Lemma fmap_ctx_proper C
    (Hle : ∀ T1 T2, ⊨T T1 <: T2 → ⊨T C T1 <: C T2) :
    Proper (ctx_sub ==> ctx_sub) (fmap C).
  Proof.
    intros G1 G2. elim: G2 G1 => [|T2 G2 IHG2] [|T1 G1] HG ρ //; cbn. *)

  #[global] Instance fmap_TLater_mono :
    Proper (ctx_sub ==> ctx_sub) (fmap TLater).
  Proof. intros xs ys Hl ?. by rewrite !env_TLater_commute (Hl _). Qed.
  #[global] Instance fmap_TLater_flip_mono :
    Proper (flip ctx_sub ==> flip ctx_sub) (fmap TLater).
  Proof. apply: flip_proper_2. Qed.

  #[global] Instance TAnd_mono : Proper (ty_sub ==> ty_sub ==> ty_sub) TAnd.
  Proof. intros x y Hl x' y' Hl' ??. by rewrite /= (Hl _ _) (Hl' _ _). Qed.
  #[global] Instance TAnd_flip_mono :
    Proper (flip ty_sub ==> flip ty_sub ==> flip ty_sub) TAnd.
  Proof. apply: flip_proper_3. Qed.

  #[global] Instance TOr_mono : Proper (ty_sub ==> ty_sub ==> ty_sub) TOr.
  Proof. intros x y Hl x' y' Hl' ??. by rewrite /= (Hl _ _) (Hl' _ _). Qed.
  #[global] Instance TOr_flip_mono :
    Proper (flip ty_sub ==> flip ty_sub ==> flip ty_sub) TOr.
  Proof. apply: flip_proper_3. Qed.

  (** Ordering of logical strength:
      unTLater T <: T <: TLater (unTLater T) <: TLater T. *)
  Lemma unTLater_ty_sub T : ⊨T unTLater T <: T.
  Proof. induction T => //=; by [ f_equiv | intros ?; auto ]. Qed.

  Lemma ty_sub_TLater_unTLater T : ⊨T T <: TLater (unTLater T).
  Proof.
    induction T; try by [iIntros (??) "$"];
      rewrite {1}IHT1 {1}IHT2 /=; intros ??;
      [> iIntros "[$ $]" | iIntros "[$|$]"].
  Qed.

  Lemma ty_sub_id T : ⊨T T <: T. Proof. done. Qed.
  Lemma ty_sub_trans T1 T2 T3 : ⊨T T1 <: T2 → ⊨T T2 <: T3 → ⊨T T1 <: T3.
  Proof. by intros ->. Qed.

  Lemma ty_sub_TLater T : ⊨T T <: TLater T.
  Proof. intros ?. auto. Qed.

  Lemma ty_sub_TLater_add T1 T2 :
    ⊨T T1 <: T2 →
    ⊨T T1 <: TLater T2.
  Proof. intros ->. apply ty_sub_TLater. Qed.

  Lemma ty_distr_TAnd_TLater T1 T2 :
    ⊨T TAnd (TLater T1) (TLater T2) <: TLater (TAnd T1 T2).
  Proof. iIntros (??) "[$ $]". Qed.

  Lemma ty_distr_TOr_TLater T1 T2 :
    ⊨T TOr (TLater T1) (TLater T2) <: TLater (TOr T1 T2).
  Proof. iIntros (??) "[$|$]". Qed.

  #[local] Hint Resolve ty_sub_id ty_sub_TLater ty_sub_TLater_add ty_sub_TLater_unTLater
    ty_distr_TAnd_TLater ty_distr_TOr_TLater unTLater_ty_sub : ctx_sub.

  (* Unused *)
  Lemma TLater_unTLater_ty_sub_TLater T :
    ⊨T TLater (unTLater T) <: TLater T.
  Proof. by rewrite unTLater_ty_sub. Qed.

  Lemma fundamental_ty_sub {T1 T2} : ⊢T T1 <: T2 → ⊨T T1 <: T2.
  Proof. induction 1; auto with f_equiv ctx_sub. exact: ty_sub_trans. Qed.
  #[local] Hint Resolve fundamental_ty_sub : ctx_sub.

  (** Lift the above ordering to environments. *)

  Lemma ctx_sub_nil : ⊨G [] <:* []. Proof. done. Qed.

  Lemma unTLater_ctx_sub Γ : ⊨G unTLater <$> Γ <:* Γ.
  Proof. eapply env_lift_sub', unTLater_ty_sub; by rewrite ?list_fmap_id. Qed.

  Lemma ctx_sub_TLater Γ : ⊨G Γ <:* TLater <$> Γ.
  Proof. eapply env_lift_sub', ty_sub_TLater; by rewrite ?list_fmap_id. Qed.

  Lemma ctx_sub_TLater_unTLater Γ : ⊨G Γ <:* TLater <$> (unTLater <$> Γ).
  Proof.
    rewrite -list_fmap_compose.
    eapply env_lift_sub', ty_sub_TLater_unTLater; by rewrite ?list_fmap_id.
  Qed.

  #[local] Hint Resolve ctx_sub_nil ctx_sub_TLater ctx_sub_TLater_unTLater unTLater_ctx_sub : ctx_sub.

  Lemma fundamental_ctx_sub {Γ1 Γ2} : ⊢G Γ1 <:* Γ2 → ⊨G Γ1 <:* Γ2.
  Proof. induction 1; auto with f_equiv ctx_sub. Qed.

  #[local] Hint Resolve fundamental_ctx_sub : ctx_sub.

  Lemma ctx_sub_cons_later T Γ1 Γ2 (Hle : ⊨G Γ1 <:* Γ2) :
    ⊨G T :: Γ1 <:* TLater T :: Γ2.
  Proof. auto with f_equiv ctx_sub. Qed.

  (* Unused *)
  Lemma TLater_unTLater_TLater_ctx_sub Γ :
    ⊨G TLater <$> (unTLater <$> Γ) <:* TLater <$> Γ.
  (* Proof. by rewrite unTLater_ctx_sub. Qed. *)
  Proof. auto with ctx_sub. Qed.

  Lemma ietp_weaken_ctx_syn Γ1 Γ2 {T e} (Hsyn : ⊢G Γ1 <:* Γ2) : Γ2 ⊨ e : T -∗ Γ1 ⊨ e : T.
  Proof. by apply ietp_mono; first apply (fundamental_ctx_sub Hsyn). Qed.

  Lemma istpd_weaken_ctx_syn Γ1 Γ2 {T1 T2 i} (Hsyn : ⊢G Γ1 <:* Γ2) :
    Γ2 ⊨ T1 <:[i] T2 -∗ Γ1 ⊨ T1 <:[i] T2.
  Proof. by apply istpd_mono; first apply (fundamental_ctx_sub Hsyn). Qed.

End CtxSub.

Typeclasses Opaque ty_sub.
Typeclasses Opaque ctx_sub.

#[global] Hint Resolve ietp_weaken_ctx_syn fundamental_ctx_sub : ctx_sub.
