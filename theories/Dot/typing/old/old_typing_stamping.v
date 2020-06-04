(** * Stamping theorem. *)
From D Require Import iris_extra.det_reduction.
From D.Dot Require Import storeless_typing core_stamping_defs ast_stamping skeleton
  path_repl_lemmas.
From D.Dot Require old_unstamped_typing old_subtyping.
From D.Dot Require Import unstampedness_binding.

Set Implicit Arguments.

Set Suggest Proof Using.
Set Default Proof Using "Type".

Notation stamps_tm'   n e__u g e__s := (stamps_tm   n AlsoNonVars e__u g e__s).
Notation stamps_dm'   n d__u g d__s := (stamps_dm   n AlsoNonVars d__u g d__s).
Notation stamps_dms'  n d__u g d__s := (stamps_dms  n AlsoNonVars d__u g d__s).
Notation stamps_path' n p__u g p__s := (stamps_path n OnlyVars  p__u g p__s).

Definition is_unstamped_to_AlsoNonVars_tm_def e : Prop := ∀ n b,
  is_unstamped_tm   n b e → is_unstamped_tm n AlsoNonVars e.
Definition is_unstamped_to_AlsoNonVars_vl_def v : Prop := ∀ n b,
  is_unstamped_vl   n b v → is_unstamped_vl n AlsoNonVars v.
Definition is_unstamped_to_AlsoNonVars_dm_def d : Prop := ∀ n b,
  is_unstamped_dm   n b d → is_unstamped_dm n AlsoNonVars d.
Definition is_unstamped_to_AlsoNonVars_path_def p : Prop := ∀ n b,
  is_unstamped_path n b p → is_unstamped_path n AlsoNonVars p.
Definition is_unstamped_to_AlsoNonVars_ty_def T : Prop := ∀ n b,
  is_unstamped_ty   n b T → is_unstamped_ty n AlsoNonVars T.

Lemma is_unstamped_to_AlsoNonVars_mut :
  (∀ t, is_unstamped_to_AlsoNonVars_tm_def t) ∧
  (∀ v, is_unstamped_to_AlsoNonVars_vl_def v) ∧
  (∀ d, is_unstamped_to_AlsoNonVars_dm_def d) ∧
  (∀ p, is_unstamped_to_AlsoNonVars_path_def p) ∧
  (∀ T, is_unstamped_to_AlsoNonVars_ty_def T).
Proof.
  apply syntax_mut_ind; intros ** ? **; with_is_unstamped inverse;
    (constructor || done); decompose_Forall; eauto 2.
Qed.

Lemma is_unstamped_ty2AlsoNonVars n b T :
  is_unstamped_ty n b T → is_unstamped_ty n AlsoNonVars T.
Proof. apply is_unstamped_to_AlsoNonVars_mut. Qed.

Lemma is_unstamped_path2AlsoNonVars n b p :
  is_unstamped_path n b p → is_unstamped_path n AlsoNonVars p.
Proof. apply is_unstamped_to_AlsoNonVars_mut. Qed.

Lemma is_unstamped_tm2AlsoNonVars n b t :
  is_unstamped_tm n b t → is_unstamped_tm n AlsoNonVars t.
Proof. apply is_unstamped_to_AlsoNonVars_mut. Qed.

Lemma is_unstamped_var2OnlyVars n x :
  is_unstamped_vl n AlsoNonVars (var_vl x) → is_unstamped_vl n OnlyVars (var_vl x).
Proof. intros; inverse_is_unstamped; eauto. Qed.

Lemma is_unstamped_path2tm n b p :
  is_unstamped_path n b p → is_unstamped_tm n b (path2tm p).
Proof.
  elim: p b => /= [v|p IHp l] b Hp; inversion Hp; simplify_eq/=; eauto.
  constructor; apply IHp. by destruct b; [| exact: is_unstamped_path2AlsoNonVars].
Qed.

Lemma is_unstamped_path2tm' n b p :
  is_unstamped_path n b p → is_unstamped_tm n AlsoNonVars (path2tm p).
Proof. intros. by eapply is_unstamped_tm2AlsoNonVars, is_unstamped_path2tm. Qed.

Section syntyping_stamping_lemmas.
  Import old_unstamped_typing storeless_typing.

  Hint Extern 5 (is_unstamped_ty _ AlsoNonVars _) =>
    try_once is_unstamped_ty2AlsoNonVars : core.
  Hint Resolve is_unstamped_path2tm' : core.
  Hint Immediate is_unstamped_var2OnlyVars is_unstamped_path2AlsoNonVars : core.

  Lemma is_unstamped_vl_lookup (Γ : ctx) x T b :
    Γ !! x = Some T → is_unstamped_vl (length Γ) b (var_vl x).
  Proof. constructor; exact: lookup_lt_Some. Qed.

  Lemma unstamped_path_subject Γ p T i:
    Γ u⊢ₚ p : T, i → is_unstamped_path' (length Γ) p.
  Proof.
    induction 1; cbn; intros; try with_is_unstamped inverse;
      eauto 7 using is_unstamped_vl_lookup.
  Qed.
  Local Hint Resolve unstamped_path_subject : core.

  Lemma unstamped_mut_subject Γ :
    (∀ e T,   Γ u⊢ₜ e : T → is_unstamped_tm (length Γ) AlsoNonVars e) ∧
    (∀ ds T,  Γ u⊢ds ds : T → is_unstamped_dms (length Γ) AlsoNonVars ds) ∧
    (∀ l d T, Γ u⊢{ l := d } : T → is_unstamped_dm (length Γ) AlsoNonVars d).
  Proof.
    eapply old_unstamped_typing_mut_ind with
        (P := λ Γ e T _, is_unstamped_tm (length Γ) AlsoNonVars e)
        (P0 := λ Γ ds T _, is_unstamped_dms (length Γ) AlsoNonVars ds)
        (P1 := λ Γ l d T _, is_unstamped_dm (length Γ) AlsoNonVars d); clear Γ;
        cbn; intros; try (rewrite <-(@ctx_strip_len Γ Γ') in *; last done);
        try by (with_is_unstamped inverse + idtac);
        eauto 7 using is_unstamped_path2tm, is_unstamped_vl_lookup.
    - elim: i {s} => [|i IHi]; rewrite /= ?iterate_0 ?iterate_S //; eauto.
    - constructor; eapply is_unstamped_path2AlsoNonVars; eauto.
  Qed.

  Section unstamped_syntyping_lemmas.

  Local Hint Resolve is_unstamped_ty_subst : core.

  (* The reverse direction slows proof search and isn't used anyway? *)
  Lemma is_unstamped_ren_ty_1 i T b:
    is_unstamped_ty i b T →
    is_unstamped_ty (S i) b (shift T).
  Proof. intros Ht. eapply is_unstamped_sub_ren_ty, Ht. auto. Qed.

  Local Hint Resolve is_unstamped_ren_ty_1 is_unstamped_nclosed_ty : core.

  Hint Extern 5 (nclosed _ _) => try_once nclosed_ren_inv_ty_one : core.
  Hint Extern 5 => try_once nclosed_sub_inv_ty_one : core.

  Inductive unstamped_ctx: ctx → Prop :=
  | unstamped_nil : unstamped_ctx []
  | unstamped_cons Γ T:
    unstamped_ctx Γ →
    is_unstamped_ty' (S (length Γ)) T →
    unstamped_ctx (T :: Γ).
  Hint Constructors unstamped_ctx : core.

  Lemma unstamped_nclosed_lookup Γ x T:
    unstamped_ctx Γ →
    Γ !! x = Some T →
    nclosed (shiftN x T) (length Γ).
  Proof.
    elim: Γ T x => // U Γ IHΓ T [Hs [<-]|x Hs Hl] /=; inverse Hs.
    - rewrite hsubst_id; eauto.
    - rewrite hrenS; eapply nclosed_sub_app, IHΓ; auto.
  Qed.
  Local Hint Resolve unstamped_nclosed_lookup : core.

  Lemma unstamped_lookup Γ x T:
    unstamped_ctx Γ → Γ !! x = Some T →
    is_unstamped_ty' (length Γ) (shiftN x T).
  Proof.
    elim: x Γ => /= [|x IHx] [|U Γ] /= Hctx Hl; inverse Hctx; simplify_eq.
    - by rewrite hsubst_id.
    - rewrite hrenS.
      apply (@is_unstamped_ren_ty_1 (length Γ) (shiftN x T)), IHx; eauto.
  Qed.

  Lemma is_unstamped_tv_inv {n v b}:
    is_unstamped_tm n b (tv v) →
    is_unstamped_vl n b v.
  Proof. by inversion 1. Qed.
  Lemma is_unstamped_TLater_inv {n T}:
    is_unstamped_ty' n (TLater T) →
    is_unstamped_ty' n T.
  Proof. by inversion 1. Qed.

  Local Hint Resolve is_unstamped_tv_inv is_unstamped_TLater_n : core.
  Local Hint Extern 5 (is_unstamped_ty _ _ _) => try_once is_unstamped_TLater_inv : core.

  Lemma fmap_TLater_unstamped_inv Γ :
    unstamped_ctx $ TLater <$> Γ →
    unstamped_ctx Γ.
  Proof.
    elim: Γ => [//|T Γ IHΓ]; cbn => Hs. inverse Hs.
    constructor; first by auto. rewrite ->(fmap_length TLater) in *.
    exact: is_unstamped_TLater_inv.
  Qed.

  Lemma fmap_TLater_unstamped Γ :
    unstamped_ctx Γ →
    unstamped_ctx $ TLater <$> Γ.
  Proof.
    elim: Γ => [//|T Γ IHΓ] Hs; cbn. inverse Hs.
    constructor; first by auto. rewrite fmap_length.
    exact: (is_unstamped_TLater_n (i := 1)).
  Qed.

  Lemma ty_strip_unstamped n T T' :
    ⊢T T >>▷ T' →
    is_unstamped_ty' n T →
    is_unstamped_ty' n T'.
  Proof. induction 1; inversion 1; auto. Qed.

  Lemma ty_sub_unstamped n T T' :
    ⊢T T <: T' →
    is_unstamped_ty' n T →
    is_unstamped_ty' n T'.
  Proof. induction 1; inversion 1; auto. Qed.

  Lemma ctx_strip_unstamped Γ Γ' :
    ⊢G Γ >>▷* Γ' →
    unstamped_ctx Γ →
    unstamped_ctx Γ'.
  Proof.
    induction 1; inversion 1; subst; constructor; first by auto.
    by erewrite <- ctx_strip_len; [exact: ty_strip_unstamped|].
  Qed.

  Lemma ctx_sub_unstamped Γ Γ' :
    ⊢G Γ <:* Γ' →
    unstamped_ctx Γ →
    unstamped_ctx Γ'.
  Proof.
    induction 1; inversion 1; subst; constructor; first by auto.
    by erewrite <- ctx_sub_len; [exact: ty_sub_unstamped|].
  Qed.

  Local Hint Resolve ctx_strip_unstamped ctx_sub_unstamped fmap_TLater_unstamped_inv : core.

  Lemma subtyping_unstamped_mut_types Γ :
    (∀ p T i, Γ u⊢ₚ p : T , i → ∀ (Hctx: unstamped_ctx Γ), is_unstamped_ty' (length Γ) T) ∧
    (∀ T1 i1 T2 i2, Γ u⊢ₜ T1, i1 <: T2, i2 → ∀ (Hctx: unstamped_ctx Γ),
      is_unstamped_ty' (length Γ) T1 ∧ is_unstamped_ty' (length Γ) T2).
  Proof.
    eapply old_pure_typing_mut_ind with
        (P := λ Γ p T i _, ∀ (Hctx: unstamped_ctx Γ), is_unstamped_ty' (length Γ) T)
        (P0 := λ Γ T1 i1 T2 i2 _, ∀ (Hctx: unstamped_ctx Γ),
               is_unstamped_ty' (length Γ) T1 ∧ is_unstamped_ty' (length Γ) T2); clear Γ.
    all: intros; simplify_eq/=; try nosplit inverse Hctx;
      try (efeed pose proof H ; [by eauto | ev; clear H ]);
      try (efeed pose proof H0; [by eauto | ev; clear H0]);
      repeat constructor; eauto 2;
      inverse_is_unstamped; eauto 4 using unstamped_lookup.
      exact /is_unstamped_ren_ty.
  Qed.
  Lemma unstamped_subtyping_types_1 Γ :
    ∀ T1 i1 T2 i2, Γ u⊢ₜ T1, i1 <: T2, i2 → ∀ (Hctx: unstamped_ctx Γ),
      is_unstamped_ty' (length Γ) T1.
  Proof. apply subtyping_unstamped_mut_types. Qed.
  Lemma unstamped_subtyping_types_2 Γ :
    ∀ T1 i1 T2 i2, Γ u⊢ₜ T1, i1 <: T2, i2 → ∀ (Hctx: unstamped_ctx Γ),
      is_unstamped_ty' (length Γ) T2.
  Proof. apply subtyping_unstamped_mut_types. Qed.
  Lemma unstamped_path_types Γ :
    (∀ p T i, Γ u⊢ₚ p : T , i → ∀ (Hctx: unstamped_ctx Γ), is_unstamped_ty' (length Γ) T).
  Proof. apply subtyping_unstamped_mut_types. Qed.

  Lemma unstamped_mut_types Γ :
    (∀ e T, Γ u⊢ₜ e : T → ∀ (Hctx: unstamped_ctx Γ), is_unstamped_ty' (length Γ) T) ∧
    (∀ ds T, Γ u⊢ds ds : T → ∀ (Hctx: unstamped_ctx Γ), is_unstamped_ty' (length Γ) T) ∧
    (∀ l d T, Γ u⊢{ l := d } : T → ∀ (Hctx: unstamped_ctx Γ), is_unstamped_ty' (length Γ) T).
  Proof.
    eapply old_unstamped_typing_mut_ind with
        (P := λ Γ e T _, ∀ (Hctx: unstamped_ctx Γ), is_unstamped_ty' (length Γ) T)
        (P0 := λ Γ ds T _, ∀ (Hctx: unstamped_ctx Γ), is_unstamped_ty' (length Γ) T)
        (P1 := λ Γ l d T _, ∀ (Hctx: unstamped_ctx Γ), is_unstamped_ty' (length Γ) T); clear Γ.
    all: intros; simplify_eq/=; try nosplit inverse Hctx;
      try (rewrite ->?(@ctx_sub_len Γ Γ'),
        ?(@ctx_strip_len Γ Γ') in * by assumption);
      try (efeed pose proof H ; [by eauto | ev; clear H ]);
      try (efeed pose proof H0; [by eauto | ev; clear H0]);
      repeat constructor; rewrite /= ?fmap_length; eauto 2;
      inverse_is_unstamped; eauto 4 using unstamped_lookup,
        is_unstamped_sub_rev_ty, unstamped_path_types,
        unstamped_subtyping_types_1, unstamped_subtyping_types_2.
  Qed.

  End unstamped_syntyping_lemmas.

  (** These hints slow down proof search. *)
  (** Not directed. *)
  Remove Hints old_subtyping.iP_Sngl_Trans : core.
  (** These cause cycles. *)
  Remove Hints old_subtyping.iP_Mu_E : core.
  Remove Hints old_subtyping.iP_Mu_I : core.
End syntyping_stamping_lemmas.
