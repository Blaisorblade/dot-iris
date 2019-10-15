From D.Dot Require Import typing typeExtractionSyn traversals stampedness closed_subst.

Set Implicit Arguments.

Section syntyping_lemmas.
  Context `{hasStampTable: stampTable}.

  Hint Constructors Forall : core.
  Lemma stamped_mut_subject Γ:
    (∀ e  T, Γ ⊢ₜ e : T → is_stamped_tm (length Γ) getStampTable e) ∧
    (∀ V ds T, Γ |ds V ⊢ ds : T → Forall (is_stamped_dm (S (length Γ)) getStampTable) (map snd ds)) ∧
    (∀ V l d T, Γ |d V ⊢{ l := d } : T → is_stamped_dm (S (length Γ)) getStampTable d) ∧
    (∀ p T i, Γ ⊢ₚ p : T, i → is_stamped_path (length Γ) getStampTable p).
  Proof.
    eapply exp_stamped_typing_mut_ind with
        (P := λ Γ e T _, is_stamped_tm (length Γ) getStampTable e)
        (P0 := λ Γ V ds T _, Forall (is_stamped_dm (S (length Γ)) getStampTable) (map snd ds))
        (P1 := λ Γ V l d T _, is_stamped_dm (S (length Γ)) getStampTable d)
        (P2 := λ Γ p T i _, is_stamped_path (length Γ) getStampTable p);
        cbn; intros; try by (with_is_stamped inverse + idtac); eauto.
    - repeat constructor => //=. by eapply lookup_lt_Some.
    - intros; elim: i {s} => [|i IHi]; rewrite /= ?iterate_0 ?iterate_S //; eauto.
    - move: e => [T' ?]; ev. by apply @Trav1.trav_dtysem with
        (T' := T') (ts' := (length σ, getStampTable)).
  Qed.

  Lemma stamped_exp_subject Γ e T: Γ ⊢ₜ e : T →
    is_stamped_tm (length Γ) getStampTable e.
  Proof. apply (stamped_mut_subject Γ). Qed.
  Lemma stamped_path_subject Γ p T i:
    Γ ⊢ₚ p : T, i → is_stamped_path (length Γ) getStampTable p.
  Proof. apply (stamped_mut_subject Γ). Qed.
  Local Hint Resolve stamped_exp_subject stamped_path_subject : core.

  (* The reverse direction slows proof search and isn't used anyway? *)
  Lemma is_stamped_ren_ty_1 i T g:
    is_stamped_ty i g T ->
    is_stamped_ty (S i) g (T.|[ren (+1)]).
  Proof. intros Ht. eapply is_stamped_sub_ty, Ht. auto. Qed.

  Local Hint Resolve
    is_stamped_ren_ty_1
    is_stamped_sub_one is_stamped_sub_one_rev
    is_stamped_nclosed_ty.

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
    nclosed T.|[ren (+x)] (length Γ).
  Proof.
    elim: Γ T x => // U Γ IHΓ T [Hs [<-]|x Hs Hl] /=; inverse Hs.
    - asimpl; eauto.
    - have ->: T.|[ren (+S x)] = T.|[ren (+x)].|[ren (+1)]. by asimpl.
      eapply nclosed_sub_app; last by eapply IHΓ.
      eapply nclosed_ren_shift; lia.
  Qed.
  Local Hint Resolve stamped_nclosed_lookup : core.

  Lemma stamped_lookup Γ x T g:
    stamped_ctx g Γ →
    Γ !! x = Some T →
    is_stamped_ty (length Γ) g T.|[ren (+x)].
  Proof.
    elim: x Γ => /= [|x IHx] [|U Γ] /= Hctx Hl; asimpl; try discriminate.
    - simplify_eq. by inverse Hctx.
    - replace (T.|[ren (+S x)]) with (T.|[ren (+x)].|[ren (+1)]); last by asimpl.
      have HstΓ: stamped_ctx g Γ. by inverse Hctx.
      eapply (@is_stamped_ren_ty_1 (length Γ) (T.|[ren (+x)]) g), IHx; eauto.
  Qed.

  Lemma is_stamped_TLater_n {i n T}:
    is_stamped_ty n getStampTable T →
    is_stamped_ty n getStampTable (iterate TLater i T).
  Proof.
    elim: i => [|//i IHi]; rewrite ?iterate_0 ?iterate_S //; auto.
  Qed.

  Lemma is_stamped_tv_inv {n v}:
    is_stamped_tm n getStampTable (tv v) →
    is_stamped_vl n getStampTable v.
  Proof. by inversion 1. Qed.
  Lemma is_stamped_TLater_inv {n T}:
    is_stamped_ty n getStampTable (TLater T) →
    is_stamped_ty n getStampTable T.
  Proof. by inversion 1. Qed.

  Local Hint Resolve is_stamped_tv_inv is_stamped_TLater_n : core.
  Local Hint Extern 5 (is_stamped_ty _ _ _) => try_once is_stamped_TLater_inv : core.

  Ltac with_is_stamped_inverse :=
    match goal with
      | H: is_stamped_ty _ _ ?T |- _ =>
        (* inversion yields many goals if [T] is a variable *)
        try (is_var T; fail 1); inverse H
    end.

  Lemma stamped_mut_types Γ :
    (∀ e T, Γ ⊢ₜ e : T → ∀ (Hctx: stamped_ctx getStampTable Γ), is_stamped_ty (length Γ) getStampTable T) ∧
    (∀ V ds T, Γ |ds V ⊢ ds : T → ∀ (Hctx: stamped_ctx getStampTable Γ), is_stamped_ty (S (length Γ)) getStampTable V →
      is_stamped_ty (S (length Γ)) getStampTable T) ∧
    (∀ V l d T, Γ |d V ⊢{ l := d } : T → ∀ (Hctx: stamped_ctx getStampTable Γ), is_stamped_ty (S (length Γ)) getStampTable V →
      is_stamped_ty (S (length Γ)) getStampTable T) ∧
    (∀ p T i, Γ ⊢ₚ p : T , i → ∀ (Hctx: stamped_ctx getStampTable Γ), is_stamped_ty (length Γ) getStampTable T) ∧
    (∀ T1 i1 T2 i2, Γ ⊢ₜ T1, i1 <: T2, i2 → ∀ (Hctx: stamped_ctx getStampTable Γ),
      is_stamped_ty (length Γ) getStampTable T1 ∧ is_stamped_ty (length Γ) getStampTable T2).
  Proof.
    eapply stamped_typing_mut_ind with
        (P := λ Γ e T _, ∀ (Hctx: stamped_ctx getStampTable Γ),
          is_stamped_ty (length Γ) getStampTable T)
        (P0 := λ Γ V ds T _, ∀ (Hctx: stamped_ctx getStampTable Γ), is_stamped_ty (S (length Γ)) getStampTable V →
          is_stamped_ty (S (length Γ)) getStampTable T)
        (P1 := λ Γ V l d T _, ∀ (Hctx: stamped_ctx getStampTable Γ), is_stamped_ty (S (length Γ)) getStampTable V →
          is_stamped_ty (S (length Γ)) getStampTable T)
        (P2 := λ Γ p T i _, ∀ (Hctx: stamped_ctx getStampTable Γ),
          is_stamped_ty (length Γ) getStampTable T)
        (P3 := λ Γ T1 i1 T2 i2 _, ∀ (Hctx: stamped_ctx getStampTable Γ),
               is_stamped_ty (length Γ) getStampTable T1 ∧ is_stamped_ty (length Γ) getStampTable T2); clear Γ.
    all: intros; cbn in *; ev; try solve [ eauto using is_stamped_ren_ty_1 ].
    all: try specialize (H Hctx); try specialize (H0 Hctx); ev.
    all: try solve [try with_is_stamped_inverse; repeat constructor; cbn; eauto 4].
    - inverse H. eapply is_stamped_sub_rev_ty => //. eauto.
    - by apply stamped_lookup.
    - have Hctx': stamped_ctx getStampTable (TLater V :: Γ). by eauto.
      move: (H Hctx') (H0 Hctx'). intuition.
    - have Hctx': stamped_ctx getStampTable (iterate TLater i T1 :: Γ).
      by eauto.
      move: (H Hctx'); intuition.
    - have Hctx': stamped_ctx getStampTable (iterate TLater (S i) T2.|[ren (+1)] :: Γ).
      by eauto.
      move: (H0 Hctx'). intros; ev; repeat econstructor; cbn; eauto.
  Qed.
End syntyping_lemmas.
