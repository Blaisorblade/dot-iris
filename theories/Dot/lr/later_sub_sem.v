(** * When is a context weaker than another? Semantic version. *)


From D Require Import proper.
From D.Dot Require Import unary_lr.
From D.Dot Require Import typing_aux_defs.

Set Suggest Proof Using.
Set Default Proof Using "Type".

(* This is specialized to [vnil] because contexts only contain proper types anyway. *)
Definition s_ty_sub `{HdlangG: !dlangG Σ} (T1 T2 : oltyO Σ 0) := ∀ ρ v, T1 vnil ρ v -∗ T2 vnil ρ v.
Notation "s⊨T T1 <: T2" := (s_ty_sub T1 T2) (at level 74, T1, T2 at next level).

Definition ty_sub `{HdlangG: !dlangG Σ} T1 T2 := s⊨T V⟦ T1 ⟧ <: V⟦ T2 ⟧.
Notation "⊨T T1 <: T2" := (ty_sub T1 T2) (at level 74, T1, T2 at next level).

Definition s_ctx_sub `{HdlangG: !dlangG Σ} (Γ1 Γ2 : sCtx Σ) : Prop := ∀ ρ, sG⟦ Γ1 ⟧* ρ -∗ sG⟦ Γ2 ⟧* ρ.
Notation "s⊨G Γ1 <:* Γ2" := (s_ctx_sub Γ1 Γ2) (at level 74, Γ1, Γ2 at next level).

Definition ctx_sub `{HdlangG: !dlangG Σ} Γ1 Γ2 : Prop := s⊨G V⟦ Γ1 ⟧* <:* V⟦ Γ2 ⟧*.
Notation "⊨G Γ1 <:* Γ2" := (ctx_sub Γ1 Γ2) (at level 74, Γ1, Γ2 at next level).

Section CtxSub.
  Context `{HdlangG: !dlangG Σ}.
  Implicit Type (T : ty) (Γ : ctx).

  (** * Basic lemmas about [s_ctx_sub]. *)
  Global Instance: RewriteRelation s_ty_sub := {}.
  Global Instance pre_s_ty_sub: PreOrder s_ty_sub.
  Proof. split; first done. by move => x y z H1 H2 ρ v; rewrite (H1 _ _). Qed.

  Global Instance: RewriteRelation ty_sub := {}.
  Global Instance: PreOrder ty_sub.
  Proof. rewrite /ty_sub; split; first done. by move => x y z H1 H2; etrans. Qed.

  Global Instance: RewriteRelation s_ctx_sub := {}.
  Global Instance: PreOrder s_ctx_sub.
  Proof. split; first done. by move => x y z H1 H2 ρ; rewrite (H1 _). Qed.

  Global Instance: RewriteRelation ctx_sub := {}.
  Global Instance: PreOrder ctx_sub.
  Proof. rewrite /ctx_sub; split; first done. by move => x y z H1 H2; etrans. Qed.

  Global Instance: Proper (equiv ==> equiv ==> iff) s_ctx_sub.
  Proof.
    rewrite /s_ctx_sub => Γ1 Γ2 HΓ Δ1 Δ2 HΔ.
    by setoid_rewrite HΔ; setoid_rewrite HΓ.
  Qed.

  Global Instance Proper_cons_s_ctx_sub : Proper (s_ty_sub ==> s_ctx_sub ==> s_ctx_sub) cons.
  Proof. move => T1 T2 HlT Γ1 Γ2 Hl ρ. cbn. by rewrite (HlT _) (Hl _). Qed.
  (* This is needed when flip ctx_sub arises from other rules. Doh. *)
  Global Instance Proper_cons_s_ctx_sub_flip :
    Proper (flip s_ty_sub ==> flip s_ctx_sub ==> flip s_ctx_sub) cons.
  Proof. solve_proper. Qed.

  Global Instance Proper_cons_ctx_sub : Proper (ty_sub ==> ctx_sub ==> ctx_sub) cons.
  Proof. rewrite /ty_sub /ctx_sub. solve_proper. Qed.
  Global Instance Proper_cons_ctx_sub_flip : Proper (flip ty_sub ==> flip ctx_sub ==> flip ctx_sub) cons.
  Proof. solve_proper. Qed.

  (** Typing is contravariant in [Γ].
  Note these instances are very specialized. *)
  Global Instance Proper_setp e : Proper (flip s_ctx_sub ==> (=) ==> (⊢)) (setp e).
  Proof. move => /= Γ1 Γ2 Hweak T1 T2 ->. by setoid_rewrite (Hweak _). Qed.
  Global Instance Proper_setp_flip e : Proper (s_ctx_sub ==> flip (=) ==> flip (⊢)) (setp e).
  Proof. apply: flip_proper_3. Qed.

  Global Instance Proper_sstpi i j : Proper (flip s_ctx_sub ==> (=) ==> (=) ==> (⊢)) (sstpi i j).
  Proof. move => /= Γ1 Γ2 Hweak T1 T2 -> U1 U2 ->. by setoid_rewrite (Hweak _). Qed.
  Global Instance Proper_sstpi_flip i j : Proper (s_ctx_sub ==> flip (=) ==> flip (=) ==> flip (⊢)) (sstpi i j).
  Proof. apply: flip_proper_4. Qed.

  Global Instance Proper_ietp : Proper (flip ctx_sub ==> (=) ==> (=) ==> (⊢)) ietp.
  Proof.
    rewrite /ctx_sub /flip /ietp => Γ1 Γ2 Hweak ??????; subst. by rewrite Hweak.
  Qed.

  Global Instance Proper_ietp_flip :
    Proper (ctx_sub ==> flip (=) ==> flip (=) ==> flip (⊢)) ietp.
  Proof. apply: flip_proper_4. Qed.

  Global Instance Proper_istpi :
    Proper (flip ctx_sub ==> (=) ==> (=) ==> (=) ==> (=) ==> (⊢)) istpi.
  Proof.
    rewrite /ctx_sub /flip /istpi => Γ1 Γ2 Hweak ????????????; subst.
    by rewrite Hweak.
  Qed.
  Global Instance Proper_istpi_flip :
    Proper (ctx_sub ==> flip (=) ==> flip (=) ==> flip (=) ==> flip (=) ==> flip (⊢)) istpi.
  Proof. apply: flip_proper_6. Qed.


  Global Instance Proper_oLater : Proper (s_ty_sub ==> s_ty_sub) oLater.
  Proof. intros x y Hl ??. by rewrite /= (Hl _ _). Qed.
  Global Instance Proper_oLater_flip :
    Proper (flip s_ty_sub ==> flip s_ty_sub) oLater.
  Proof. apply: flip_proper_2. Qed.

  Global Instance Proper_TLater : Proper (ty_sub ==> ty_sub) TLater.
  Proof. by rewrite /ty_sub => ?? /= ->. Qed.
  Global Instance Proper_TLater_flip :
    Proper (flip ty_sub ==> flip ty_sub) TLater.
  Proof. apply: flip_proper_2. Qed.

  Lemma senv_TLater_commute (Γ : sCtx Σ) ρ : sG⟦ oLater <$> Γ ⟧* ρ ⊣⊢ ▷ sG⟦ Γ ⟧* ρ.
  Proof.
    elim: Γ ρ => [| T Γ IH] ρ; cbn; [|rewrite IH later_and];
      iSplit; by [iIntros "$" | iIntros "_"].
  Qed.

  Lemma fmap_TLater_oLater Γ : V⟦ TLater <$> Γ ⟧* = oLater <$> V⟦ Γ ⟧*.
  Proof. elim: Γ => [//| T Γ IH]; cbn. by rewrite IH. Qed.

  Lemma env_TLater_commute Γ ρ : G⟦ TLater <$> Γ ⟧ ρ ⊣⊢ ▷ G⟦ Γ ⟧ ρ.
  Proof. by rewrite -senv_TLater_commute fmap_TLater_oLater. Qed.

  (** The strength ordering of contexts lifts the strength ordering of types. *)
  Lemma env_lift_sub f g {Γ} (Hle: ∀ T, ⊨T f T <: g T):
    ⊨G f <$> Γ <:* g <$> Γ.
  Proof. elim: Γ => [//| T Γ IH] ρ; cbn. by rewrite (Hle T _ _) -(IH _). Qed.

  Lemma env_lift_sub' f g Γ {Γ1 Γ2}:
    Γ1 = f <$> Γ → Γ2 = g <$> Γ →
    (∀ T, ⊨T f T <: g T) →
    ⊨G Γ1 <:* Γ2.
  Proof. move => -> -> Hweak. exact: env_lift_sub. Qed.

  (* It's not immediate to generalize Proper_fmap_TLater to [fmap C] for a
  type constructor [C]. Fpr instance, the following is hopeless. *)
  (* Lemma Proper_fmap_ctx C
    (Hle: ∀ T1 T2, ⊨T T1 <: T2 → ⊨T C T1 <: C T2):
    Proper (ctx_sub ==> ctx_sub) (fmap C).
  Proof.
    intros G1 G2. elim: G2 G1 => [|T2 G2 IHG2] [|T1 G1] HG ρ //; cbn. *)

  Global Instance Proper_fmap_TLater :
    Proper (ctx_sub ==> ctx_sub) (fmap TLater).
  Proof. intros xs ys Hl ?. by rewrite !env_TLater_commute (Hl _). Qed.
  Global Instance Proper_fmap_TLater_flip :
    Proper (flip ctx_sub ==> flip ctx_sub) (fmap TLater).
  Proof. apply: flip_proper_2. Qed.

  Global Instance Proper_TAnd : Proper (ty_sub ==> ty_sub ==> ty_sub) TAnd.
  Proof. intros x y Hl x' y' Hl' ??. by rewrite /= (Hl _ _) (Hl' _ _). Qed.
  Global Instance Proper_TAnd_flip :
    Proper (flip ty_sub ==> flip ty_sub ==> flip ty_sub) TAnd.
  Proof. apply: flip_proper_3. Qed.

  Global Instance Proper_TOr : Proper (ty_sub ==> ty_sub ==> ty_sub) TOr.
  Proof. intros x y Hl x' y' Hl' ??. by rewrite /= (Hl _ _) (Hl' _ _). Qed.
  Global Instance Proper_TOr_flip :
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

  Hint Resolve ty_sub_id ty_sub_TLater ty_sub_TLater_add ty_sub_TLater_unTLater
    ty_distr_TAnd_TLater ty_distr_TOr_TLater unTLater_ty_sub : ctx_sub.

  (* Unused *)
  Lemma TLater_unTLater_ty_sub_TLater T :
    ⊨T TLater (unTLater T) <: TLater T.
  Proof. by rewrite unTLater_ty_sub. Qed.

  Lemma fundamental_ty_sub {T1 T2} : ⊢T T1 <: T2 → ⊨T T1 <: T2.
  Proof. induction 1; auto with f_equiv ctx_sub. exact: ty_sub_trans. Qed.
  Hint Resolve fundamental_ty_sub : ctx_sub.

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

  Hint Resolve ctx_sub_nil ctx_sub_TLater ctx_sub_TLater_unTLater unTLater_ctx_sub : ctx_sub.

  Lemma fundamental_ctx_sub {Γ1 Γ2} : ⊢G Γ1 <:* Γ2 → ⊨G Γ1 <:* Γ2.
  Proof. induction 1; auto with f_equiv ctx_sub. Qed.

  Local Hint Resolve fundamental_ctx_sub : ctx_sub.

  Lemma ctx_sub_cons_id_syn T Γ1 Γ2 :
    ⊢G Γ1 <:* Γ2 → ⊢G T :: Γ1 <:* T :: Γ2.
  Proof. auto with ctx_sub. Qed.

  Lemma ctx_sub_cons_later_syn T Γ1 Γ2 :
    ⊢G Γ1 <:* Γ2 → ⊢G T :: Γ1 <:* TLater T :: Γ2.
  Proof. auto with ctx_sub. Qed.

  Lemma ctx_sub_cons_later T Γ1 Γ2 (Hle : ⊨G Γ1 <:* Γ2) :
    ⊨G T :: Γ1 <:* TLater T :: Γ2.
  Proof. auto with f_equiv ctx_sub. Qed.

  Lemma TLater_unTLater_TLater_ctx_sub_syn Γ :
    ⊢G TLater <$> (unTLater <$> Γ) <:* TLater <$> Γ.
  Proof. auto with ctx_sub. Qed.

  (* Unused *)
  Lemma TLater_unTLater_TLater_ctx_sub Γ :
    ⊨G TLater <$> (unTLater <$> Γ) <:* TLater <$> Γ.
  (* Proof. by rewrite unTLater_ctx_sub. Qed. *)
  Proof. auto with ctx_sub. Qed.

  Lemma ietp_weaken_ctx_syn Γ1 Γ2 {T e} (Hsyn : ⊢G Γ1 <:* Γ2) : Γ2 ⊨ e : T -∗ Γ1 ⊨ e : T.
  Proof. by apply Proper_ietp; first apply (fundamental_ctx_sub Hsyn). Qed.

  Lemma istpi_weaken_ctx_syn Γ1 Γ2 {T1 T2 i j} (Hsyn : ⊢G Γ1 <:* Γ2) :
    Γ2 ⊨ T1, i <: T2, j -∗ Γ1 ⊨ T1, i <: T2, j.
  Proof. by apply Proper_istpi; first apply (fundamental_ctx_sub Hsyn). Qed.
End CtxSub.

Typeclasses Opaque s_ty_sub.
Typeclasses Opaque ty_sub.
Typeclasses Opaque s_ctx_sub.
Typeclasses Opaque ctx_sub.

Hint Resolve ietp_weaken_ctx_syn fundamental_ctx_sub : ctx_sub.
