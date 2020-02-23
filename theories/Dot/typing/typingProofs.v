From D Require Import prelude.
From D.Dot Require Import typeExtractionSyn traversals stampedness_binding closed_subst.
From D.Dot Require Import typing_storeless.
Set Implicit Arguments.

Set Suggest Proof Using.
Set Default Proof Using "Type".

Section storeless_syntyping_lemmas.
  Lemma stamped_mut_subject Γ g :
    (∀ e T, Γ v⊢ₜ[ g ] e : T → is_stamped_tm (length Γ) g e) ∧
    (∀ ds T, Γ v⊢ds[ g ] ds : T → Forall (is_stamped_dm (length Γ) g) (map snd ds)) ∧
    (∀ l d T, Γ v⊢[ g ]{ l := d } : T → is_stamped_dm (length Γ) g d) ∧
    (∀ p T i, Γ v⊢ₚ[ g ] p : T, i → is_stamped_path (length Γ) g p).
  Proof.
    eapply exp_storeless_typing_mut_ind with
        (P := λ Γ g e T _, is_stamped_tm (length Γ) g e)
        (P0 := λ Γ g ds T _, Forall (is_stamped_dm (length Γ) g) (map snd ds))
        (P1 := λ Γ g l d T _, is_stamped_dm (length Γ) g d)
        (P2 := λ Γ g p T i _, is_stamped_path (length Γ) g p); clear Γ g;
        cbn; intros; try (rewrite <-(@ctx_sub_len_tlater Γ Γ') in *; last done);
        try by (with_is_stamped inverse + idtac); eauto using is_stamped_path2tm.
    - repeat constructor => //=. by eapply lookup_lt_Some.
    - intros; elim: i {s} => [|i IHi]; rewrite /= ?iterate_0 ?iterate_S //; eauto.
    - move: e => [T' ?]; ev. by apply @Trav1.trav_dtysem with
        (T' := T') (ts' := (length σ, g)).
  Qed.

  Lemma stamped_exp_subject Γ g e T: Γ v⊢ₜ[ g ] e : T →
    is_stamped_tm (length Γ) g e.
  Proof. apply stamped_mut_subject. Qed.
  Lemma stamped_path_subject Γ g p T i:
    Γ v⊢ₚ[ g ] p : T, i → is_stamped_path (length Γ) g p.
  Proof. apply stamped_mut_subject. Qed.

  (* The reverse direction slows proof search and isn't used anyway? *)
  Lemma is_stamped_ren_ty_1 i T g:
    is_stamped_ty i g T ->
    is_stamped_ty (S i) g (shift T).
  Proof. intros Ht. eapply is_stamped_sub_ty, Ht. auto. Qed.

  Local Hint Resolve
    is_stamped_ren_ty_1
    is_stamped_sub_one is_stamped_sub_one_rev
    is_stamped_nclosed_ty : core.

  Hint Extern 5 (nclosed _ _) => try_once nclosed_ren_inv_ty_one : core.
  Hint Extern 5 => try_once nclosed_sub_inv_ty_one : core.

  Inductive stamped_ctx g: ctx → Prop :=
  | stamped_nil : stamped_ctx g []
  | stamped_cons Γ T:
    stamped_ctx g Γ →
    is_stamped_ty (S (length Γ)) g T →
    stamped_ctx g (T :: Γ).
  Hint Constructors stamped_ctx : core.

  Lemma stamped_nclosed_lookup Γ x T g:
    stamped_ctx g Γ →
    Γ !! x = Some T →
    nclosed (shiftN x T) (length Γ).
  Proof.
    elim: Γ T x => // U Γ IHΓ T [Hs [<-]|x Hs Hl] /=; inverse Hs.
    - rewrite hsubst_id; eauto.
    - rewrite hrenS; eapply nclosed_sub_app, IHΓ; auto.
  Qed.
  Local Hint Resolve stamped_nclosed_lookup : core.

  Lemma stamped_lookup Γ x T g:
    stamped_ctx g Γ → Γ !! x = Some T →
    is_stamped_ty (length Γ) g (shiftN x T).
  Proof.
    elim: x Γ => /= [|x IHx] [|U Γ] /= Hctx Hl; inverse Hctx; simplify_eq.
    - by rewrite hsubst_id.
    - rewrite hrenS.
      apply (@is_stamped_ren_ty_1 (length Γ) (shiftN x T) g), IHx; eauto.
  Qed.

  Lemma is_stamped_TLater_n {i n T g}:
    is_stamped_ty n g T →
    is_stamped_ty n g (iterate TLater i T).
  Proof. elim: i => [|//i IHi]; rewrite ?iterate_0 ?iterate_S //; auto. Qed.

  Lemma is_stamped_tv_inv {n v g}:
    is_stamped_tm n g (tv v) →
    is_stamped_vl n g v.
  Proof. by inversion 1. Qed.
  Lemma is_stamped_TLater_inv {n T g}:
    is_stamped_ty n g (TLater T) →
    is_stamped_ty n g T.
  Proof. by inversion 1. Qed.

  Local Hint Resolve is_stamped_tv_inv is_stamped_TLater_n : core.
  Local Hint Extern 5 (is_stamped_ty _ _ _) => try_once is_stamped_TLater_inv : core.

  Lemma fmap_TLater_stamped_inv Γ g :
    stamped_ctx g $ TLater <$> Γ →
    stamped_ctx g Γ.
  Proof.
    elim: Γ => [//|T Γ IHΓ]; cbn => Hs. inverse Hs.
    constructor; first by auto. rewrite ->(fmap_length TLater) in *.
    exact: is_stamped_TLater_inv.
  Qed.

  Lemma fmap_TLater_stamped Γ g :
    stamped_ctx g Γ →
    stamped_ctx g $ TLater <$> Γ.
  Proof.
    elim: Γ => [//|T Γ IHΓ] Hs; cbn. inverse Hs.
    constructor; first by auto. rewrite fmap_length.
    exact: (is_stamped_TLater_n (i := 1)).
  Qed.

  Lemma ty_sub_stamped n g T T' :
    ⊢T T <: T' ->
    is_stamped_ty n g T →
    is_stamped_ty n g T'.
  Proof. induction 1; inversion 1; eauto. Qed.

  Lemma ctx_sub_stamped Γ Γ' g :
    ⊢G Γ <:* Γ' ->
    stamped_ctx g Γ →
    stamped_ctx g Γ'.
  Proof.
    induction 1; inversion 1; subst; constructor; first by auto.
    by erewrite <- ctx_sub_len; [exact: ty_sub_stamped|].
  Qed.

  Local Hint Resolve ctx_sub_stamped fmap_TLater_stamped_inv : core.

  Local Hint Resolve stamped_exp_subject stamped_path_subject : core.
  Lemma stamped_mut_types Γ g :
    (∀ e T, Γ v⊢ₜ[ g ] e : T → ∀ (Hctx: stamped_ctx g Γ), is_stamped_ty (length Γ) g T) ∧
    (∀ ds T, Γ v⊢ds[ g ] ds : T → ∀ (Hctx: stamped_ctx g Γ), is_stamped_ty (length Γ) g T) ∧
    (∀ l d T, Γ v⊢[ g ]{ l := d } : T → ∀ (Hctx: stamped_ctx g Γ), is_stamped_ty (length Γ) g T) ∧
    (∀ p T i, Γ v⊢ₚ[ g ] p : T , i → ∀ (Hctx: stamped_ctx g Γ), is_stamped_ty (length Γ) g T) ∧
    (∀ T1 i1 T2 i2, Γ v⊢ₜ[ g ] T1, i1 <: T2, i2 → ∀ (Hctx: stamped_ctx g Γ),
      is_stamped_ty (length Γ) g T1 ∧ is_stamped_ty (length Γ) g T2).
  Proof.
    eapply storeless_typing_mut_ind with
        (P := λ Γ g e T _, ∀ (Hctx: stamped_ctx g Γ), is_stamped_ty (length Γ) g T)
        (P0 := λ Γ g ds T _, ∀ (Hctx: stamped_ctx g Γ), is_stamped_ty (length Γ) g T)
        (P1 := λ Γ g l d T _, ∀ (Hctx: stamped_ctx g Γ), is_stamped_ty (length Γ) g T)
        (P2 := λ Γ g p T i _, ∀ (Hctx: stamped_ctx g Γ), is_stamped_ty (length Γ) g T)
        (P3 := λ Γ g T1 i1 T2 i2 _, ∀ (Hctx: stamped_ctx g Γ),
               is_stamped_ty (length Γ) g T1 ∧ is_stamped_ty (length Γ) g T2); clear Γ g.
    all: intros; simplify_eq/=; try nosplit inverse Hctx;
      try (rewrite ->?(@ctx_sub_len Γ Γ'),
        ?(@ctx_sub_len_tlater Γ Γ') in * by assumption);
      try (efeed pose proof H ; [by eauto | ev; clear H ]);
      try (efeed pose proof H0; [by eauto | ev; clear H0]);
      repeat constructor; rewrite /= ?fmap_length; eauto 2;
      inverse_is_stamped; eauto 4 using stamped_lookup, is_stamped_sub_rev_ty.
  Qed.
End storeless_syntyping_lemmas.
