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

  Lemma is_unstamped_TLater_n {i n T}:
    is_unstamped_ty' n T →
    is_unstamped_ty' n (iterate TLater i T).
  Proof. elim: i => [|//i IHi]; rewrite ?iterate_0 ?iterate_S //; auto. Qed.

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

  Implicit Types (L T U V : ty) (v : vl) (e : tm) (d : dm) (p: path) (ds : dms) (Γ : list ty) (g : stys).

  Lemma stamped_obj_ident_typing_mono_mut Γ g :
    (∀ e T, Γ s⊢ₜ[ g ] e : T → ∀ g' (Hle : g ⊆ g'), Γ s⊢ₜ[ g' ] e : T) ∧
    (∀ ds T, Γ s⊢ds[ g ] ds : T → ∀ g' (Hle : g ⊆ g'), Γ s⊢ds[ g' ] ds : T) ∧
    (∀ l d T, Γ s⊢[ g ]{ l := d } : T → ∀ g' (Hle : g ⊆ g'), Γ s⊢[ g' ]{ l := d } : T) ∧
    (∀ p T i, Γ s⊢ₚ[ g ] p : T, i → ∀ g' (Hle : g ⊆ g'), Γ s⊢ₚ[ g' ] p : T, i) ∧
    (∀ T1 i1 T2 i2, Γ s⊢ₜ[ g ] T1, i1 <: T2, i2 → ∀ g' (Hle : g ⊆ g'), Γ s⊢ₜ[ g' ] T1, i1 <: T2, i2).
  Proof.
    eapply storeless_typing_mut_ind with
        (P := λ Γ g e T _, ∀ g' (Hle : g ⊆ g'), Γ s⊢ₜ[ g' ] e : T)
        (P0 := λ Γ g ds T _, ∀ g' (Hle : g ⊆ g'), Γ s⊢ds[ g' ] ds : T)
        (P1 := λ Γ g l d T _, ∀ g' (Hle : g ⊆ g'), Γ s⊢[ g' ]{ l := d } : T)
        (P2 := λ Γ g p T i _, ∀ g' (Hle : g ⊆ g'), Γ s⊢ₚ[ g' ] p : T, i)
        (P3 := λ Γ g T1 i1 T2 i2 _, ∀ g' (Hle : g ⊆ g'), Γ s⊢ₜ[ g' ] T1, i1 <: T2, i2);
    clear Γ g; intros;
      repeat match goal with
      | H : forall g : stys, _ |- _ => specialize (H g' Hle)
      end; eauto 3; eauto.
  Qed.
  Lemma stamped_obj_ident_typed_mono Γ (g g' : stys) (Hle: g ⊆ g') e T:
    Γ s⊢ₜ[ g ] e : T → Γ s⊢ₜ[ g' ] e : T.
  Proof. unmut_lemma (stamped_obj_ident_typing_mono_mut Γ g). Qed.
  Lemma stamped_obj_ident_subtype_mono Γ (g g' : stys) (Hle: g ⊆ g') T1 i1 T2 i2:
    Γ s⊢ₜ[ g ] T1, i1 <: T2, i2 → Γ s⊢ₜ[ g' ] T1, i1 <: T2, i2.
  Proof. unmut_lemma (stamped_obj_ident_typing_mono_mut Γ g). Qed.

  Lemma stamped_obj_ident_dms_typed_mono Γ (g g' : stys) (Hle: g ⊆ g'):
    ∀ ds T, Γ s⊢ds[ g ] ds : T → Γ s⊢ds[ g' ] ds : T.
  Proof. unmut_lemma (stamped_obj_ident_typing_mono_mut Γ g). Qed.
  Lemma stamped_obj_ident_dm_typed_mono Γ (g g' : stys) (Hle: g ⊆ g'):
    ∀ l d T, Γ s⊢[ g ]{ l := d } : T → Γ s⊢[ g' ]{ l := d } : T.
  Proof. unmut_lemma (stamped_obj_ident_typing_mono_mut Γ g). Qed.
  Lemma stamped_obj_ident_path_typed_mono Γ (g g' : stys) (Hle: g ⊆ g'):
    ∀ p T i, Γ s⊢ₚ[ g ] p : T, i → Γ s⊢ₚ[ g' ] p : T, i.
  Proof. unmut_lemma (stamped_obj_ident_typing_mono_mut Γ g). Qed.

  Hint Extern 5 => try_once stamped_obj_ident_typed_mono : core.
  Hint Extern 5 => try_once stamped_obj_ident_dms_typed_mono : core.
  Hint Extern 5 => try_once stamped_obj_ident_dm_typed_mono : core.
  Hint Extern 5 => try_once stamped_obj_ident_path_typed_mono : core.
  Hint Extern 5 => try_once stamped_obj_ident_subtype_mono : core.

  Hint Extern 5 => try_once is_stamped_mono_tm : core.
  Hint Extern 5 => try_once stamps_unstamp_mono_tm : core.
  Hint Extern 5 => try_once is_stamped_mono_dm : core.
  Hint Extern 5 => try_once stamps_unstamp_mono_dm : core.

  Hint Resolve unstamped_stamped_type var_stamps_to_self path_stamps_to_self : core.
  Hint Extern 998 (_ = _) => f_equal : core.

  Local Ltac lte g g1 g2 := have ?: g ⊆ g2 by trans g1.

  Hint Resolve is_stamped_path2tm is_unstamped_path2tm unstamp_path2tm : core.
  Hint Resolve unstamped_stamped_path unstamped_stamps_self_path : core.

  Hint Resolve psubst_one_implies is_unstamped_ty_subst : core.
  (** These hints slow down proof search. *)
  (** Not directed. *)
  Remove Hints storeless_typing.iP_Sngl_Trans : core.
  (** These cause cycles. *)
  Remove Hints storeless_typing.iP_Mu_E : core.
  Remove Hints storeless_typing.iP_Mu_I : core.

  (* To guard against loops. *)
  Tactic Notation "naive_solver" := timeout 1 naive_solver.

  (* This allows stamped paths to change; that's not used for paths appearing
  in types, and it helps stamp D-Val/D-Val-New. *)
  Lemma stamp_obj_ident_subtyping_mut Γ :
    (∀ p T i, Γ u⊢ₚ p : T, i →
      ∀ g, ∃ g',
      Γ s⊢ₚ[ g' ] p : T, i
        ∧ g ⊆ g') ∧
    (∀ T1 i1 T2 i2, Γ u⊢ₜ T1, i1 <: T2, i2 →
      ∀ g, ∃ g', Γ s⊢ₜ[ g' ] T1, i1 <: T2, i2 ∧ g ⊆ g').
  Proof.
    eapply old_pure_typing_mut_ind with
      (P := λ Γ p T i _, ∀ g, ∃ g',
        Γ s⊢ₚ[ g' ] p : T, i ∧ g ⊆ g')
      (P0 := λ Γ T1 i1 T2 i2 _, ∀ g, ∃ g',
        Γ s⊢ₜ[ g' ] T1, i1 <: T2, i2 ∧ g ⊆ g');
       clear Γ.
    all: try solve [intros * Hu1 IHs1 Hu2 IHs2 g;
    (* Strategy for cases of subtyping with multiple premises:
        - apply the induction hypothesis on the first premise with map [g], and obtain map [g1];
        - apply the induction hypothesis on the second premise with map [g1], and obtain map [g2];
        - exhibit map [g2]. *)
    (* Specialize IHs1 (with [/(.$ g]) and split the result. Ditto IHs2. *)
      move: IHs1 => /(.$ g) [g1 [IHs1 Hle1]];
      move: IHs2 => /(.$ g1) [g2 [IHs2 Hle2]]; ev; lte g g1 g2;
      exists g2; split_and!; try fast_done; eauto 3].
    all: try solve [intros * Hu1 IHs1 **;
      move: IHs1 => /(.$ g) [g1 [Hts1 Hle1]]; exists g1; split_and!;
      try fast_done; (constructor; eauto 2) || eauto 3].
    all: try solve [intros; exists g; split_and!; try fast_done; constructor; eauto 2].
  - intros * Hus1 Hu1 IHs1 g.
    move: IHs1 => /(.$ g) /= [g1 ?]; ev.
    exists g1; split_and! => //; econstructor; naive_solver.
  - intros * Hus1 Hu1 IHs1 g.
    move: IHs1 => /(.$ g) /= [g1 ?]; ev.
    have ?: is_unstamped_path' (length Γ) p. exact: unstamped_path_subject.
    exists g1; split_and! => //. econstructor; naive_solver.
  - intros * Hu1 IHs1 Hu2 IHs2 g.
    move: IHs1 => /(.$ g) [g1 [Hs1 ?]].
    move: IHs2 => /(.$ g1) [g2 [Hs2 ?]]; ev; lte g g1 g2.
    exists g2; split_and! => //; eapply storeless_typing.iP_Sngl_Trans => //.
    naive_solver.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) [g1 ?]; ev.
    exists g1; split_and! => //.
    exact: storeless_typing.iSel_Sub.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) [g1 ?]; ev.
    exists g1; split_and! => //.
    exact: storeless_typing.iSub_Sel.
  - intros * Hpr Hus1 Hus2 Hu1 IHs1 g.
    move: IHs1 => /(.$ g) [g1 ?]; ev.
    exists g1; split_and! => //.
    eapply storeless_typing.iSngl_pq_Sub; eauto 2.
  - intros * Hu1 IHs1 Hu2 IHs2 Hus1 g.
    move: IHs1 => /(.$ g) [g1 [Hts1 Hle1]];
    move: IHs2 => /(.$ g1) [g2 [Hts2 Hle2]]; lte g g1 g2.
    exists g2; split_and! => //.
    apply storeless_typing.iAll_Sub_All; eauto 2.
  - intros * Hus1 Hu1 IHs1 g.
    move: IHs1 => /(.$ g) [g1 [Hts1 Hle1]].
    exists g1; split_and! => //.
    eauto.
  Qed.

  Lemma stamp_obj_ident_path_typing Γ :
    (∀ p T i, Γ u⊢ₚ p : T, i →
      ∀ g, ∃ g', Γ s⊢ₚ[ g' ] p : T, i ∧ g ⊆ g').
  Proof. apply stamp_obj_ident_subtyping_mut. Qed.
  Lemma stamp_obj_ident_subtyping Γ :
    (∀ T1 i1 T2 i2, Γ u⊢ₜ T1, i1 <: T2, i2 →
      ∀ g, ∃ g', Γ s⊢ₜ[ g' ] T1, i1 <: T2, i2 ∧ g ⊆ g').
  Proof. apply stamp_obj_ident_subtyping_mut. Qed.
  Local Hint Resolve stamp_obj_ident_subtyping stamp_obj_ident_path_typing : core.

  Lemma stamp_obj_ident_typing_mut Γ :
    (∀ e T, Γ u⊢ₜ e : T →
      ∀ g, ∃ e' g',
      Γ s⊢ₜ[ g' ] e' : T ∧ g ⊆ g' ∧ stamps_tm' (length Γ) e g' e') ∧
    (∀ ds T, Γ u⊢ds ds : T →
      ∀ g, ∃ ds' g',
      Γ s⊢ds[ g' ] ds' : T ∧ g ⊆ g' ∧ stamps_dms' (length Γ) ds g' ds') ∧
    (∀ l d T, Γ u⊢{ l := d } : T →
      ∀ g, ∃ d' g',
      Γ s⊢[ g' ]{ l := d' } : T
        ∧ g ⊆ g' ∧ stamps_dm' (length Γ) d g' d').
  Proof.
    eapply old_unstamped_typing_mut_ind with
      (P := λ Γ e T _, ∀ g, ∃ e' g',
        Γ s⊢ₜ[ g' ] e' : T ∧ g ⊆ g' ∧ stamps_tm' (length Γ) e g' e')
      (P0 := λ Γ ds T _, ∀ g, ∃ ds' g',
        Γ s⊢ds[ g' ] ds' : T ∧ g ⊆ g' ∧ stamps_dms' (length Γ) ds g' ds')
      (P1 := λ Γ l d T _, ∀ g, ∃ d' g',
        Γ s⊢[ g' ]{ l := d' } : T ∧ g ⊆ g' ∧
        stamps_dm' (length Γ) d g' d');
       clear Γ.

    all: try solve [intros * Hu1 IHs1 Hu2 IHs2 g;
    (* Strategy for cases of subtyping with multiple premises:
        - apply the induction hypothesis on the first premise with map [g], and obtain map [g1];
        - apply the induction hypothesis on the second premise with map [g1], and obtain map [g2];
        - exhibit map [g2]. *)
    (* Specialize IHs1 (with [/(.$ g]) and split the result. Ditto IHs2. *)
      move: IHs1 => /(.$ g) [g1 [IHs1 Hle1]];
      move: IHs2 => /(.$ g1) [g2 [IHs2 Hle2]]; ev; lte g g1 g2;
      exists g2; split_and!; try fast_done; eauto 3].
    all: try solve [intros * Hu1 IHs1 **;
      move: IHs1 => /(.$ g) [g1 [Hts1 Hle1]]; exists g1; split_and!;
      try fast_done; (constructor; eauto 2) || eauto 3].
    all: try solve [intros; exists g; split_and!; try fast_done; constructor; eauto 2].

  (* In hyp names, [Hus] are for [is_unstamped_ty], [Husp] for
  [is_unstamped_path], [Hu] for unstamped typing, [IHs] for the induction
  hyps about stamped typing, [Hle] for [g? ⊆ g?], [Hpr] for path replacement. *)
  - intros * Husp Hu1 IHs1 Hu2 g.
    move: IHs1 => /(.$ g) [e1' [g1 [IHs1 [Hle1 Hse1]]]].
    move: (stamp_obj_ident_path_typing Hu2) => /(.$ g1) [g2 [IHs2 Hle2]]; lte g g1 g2.
    have Hse1': unstamp_tm g2 e1' = e1. by eapply stamps_unstamp_mono_tm, Hse1.
    exists (tapp e1' (path2tm p2)), g2.
    split_and!; first eapply storeless_typing.iT_All_Ex_p => //; naive_solver eauto 6.
  - intros * Hu1 IHs1 Hu2 IHs2 g.
    move: IHs1 => /(.$ g) [e1' [g1 ?]];
    move: IHs2 => /(.$ g1) [e2' [g2 ?]]; ev; lte g g1 g2.
    exists (tapp e1' e2'), g2; naive_solver.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) [e1' [g1 ?]].
    exists (tproj e1' l), g1; naive_solver.
  - intros * Hctxsub Hus1 Hu1 IHs1 g.
    move: IHs1 => /(.$ g) [e' [g1 ?]].
    exists (tv (vabs e')), g1.
    simpl in *. rewrite <-(ctx_strip_len Hctxsub) in *.
    naive_solver.
  - intros * Huds1 IHs1 Hus1 g.
    move: IHs1 => /(.$ g) [ds' [g1 ?]].
    exists (tv (vobj ds')), g1; naive_solver.
  - intros * Hu1 ? IHs2 g.
    move: (stamp_obj_ident_subtyping Hu1) => /(.$ g) [g1 [Hts1 Hle1]].
    move: IHs2 => /(.$ g1) [e' [g2 [Hts2 [Hle2 Hs]]]]; lte g g1 g2.
    eapply stamps_tm_skip with (i := i) in Hs.
    exists (iterate tskip i e'), g2; eauto.
  - intros * Hu1 g.
    move: (stamp_obj_ident_path_typing Hu1) => /(.$ g) /= [g1 ?]; ev.
    have ? := unstamped_path_subject Hu1.
    exists (path2tm p), g1; naive_solver.
  - intros. exists (tv (vint n)), g; split_and?; try typconstructor; naive_solver.
  - intros. exists (tv (vbool b)), g; split_and?; try typconstructor; naive_solver.
  - intros * Hprim Hu1 IHs1 g.
    move: IHs1 => /(.$ g) [e1' [g1 ?]].
    exists (tun u e1'), g1; naive_solver.
  - intros * Hprim Hu1 IHs1 Hu2 IHs2 g.
    move: IHs1 => /(.$ g) [e1' [g1 [Hts1 [Hle1 ?]]]].
    move: IHs2 => /(.$ g1) [e2' [g2 [Hts2 [Hle2 ?]]]].
    have ?: unstamp_tm g2 e1' = e1 by exact: stamps_unstamp_mono_tm.
    (* Must come *after* the assertion. *)
    lte g g1 g2; ev.
    exists (tbin b e1' e2'), g2; cbn; split_and!; first econstructor; eauto 3.
  - intros * Hu1 IHs1 Hu2 IHs2 Hu3 IHs3 g.
    move: IHs1 => /(.$ g) [e' [g1 [Hts1 [Hle1 ?]]]].
    move: IHs2 => /(.$ g1) [e1' [g2 [Hts2 [Hle2 ?]]]].
    move: IHs3 => /(.$ g2) [e2' [g3 [Hts3 [Hle3 ?]]]].
    lte g g1 g2; lte g1 g2 g3; lte g g1 g3; ev.
    exists (tif e' e1' e2'), g3; cbn; split_and!; try f_equal; naive_solver.
  - intros; exists [], g; naive_solver.
  - intros * Hu1 IHs1 Hu2 IHs2 ? g.
    move: IHs1 => /(.$ g) [d' [g1 ?]].
    move: IHs2 => /(.$ g1) [ds' [g2 ?]]; ev; lte g g1 g2.
    have ?: unstamp_dm g2 d' = d by naive_solver.
    exists ((l, d') :: ds'), g2; cbn.
    split_and!; eauto 4 using unstamp_dms_hasnt.

    (* The core and most interesting case! Stamping dtysyn! *)
  - intros * Hus Hu1 Hu2 g.
    move: (stamp_obj_ident_subtyping Hu1) => /(.$ g) [g1 [Hts1 Hle1]];
    move: (stamp_obj_ident_subtyping Hu2) => /(.$ g1) [g2 [Hts2 Hle2]].

    have Husv: is_unstamped_dm (length Γ) AlsoNonVars (dtysyn T) by eauto.
    destruct (extract g2 (length Γ) T) as [g3 [s σ]] eqn:Heqo.
    move: Heqo => [Heqg3 Heqs Heqσ].
    have {Heqσ} -Heqσ: σ = idsσ (length Γ) by naive_solver.
    destruct (stamp_dtysyn_spec g2 Husv); destruct_and!.
    have ?: g2 ⊆ g3 by simplify_eq. lte g g1 g2; lte g g2 g3; lte g1 g2 g3.
    exists (dtysem σ s), g3; simplify_eq; split_and!;
      first eapply (storeless_typing.iD_Typ_Abs T); auto 2; [
        exact: (stamped_obj_ident_subtype_mono _ Hts1)|
        exact: (stamped_obj_ident_subtype_mono _ Hts2)].
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) /= [e1' [g1 ?]]; destruct_and!.
    have [v' ?]: ∃ v', e1' = tv v' by destruct e1'; naive_solver.
    simplify_eq/=; with_is_stamped inverse; with_is_unstamped inverse.
    exists (dpt (pv v')), g1; naive_solver.
  - intros * Hu1 g.
    move: (stamp_obj_ident_path_typing Hu1) => /(.$ g) /= [g1 ?]; destruct_and!.
    exists (dpt p), g1; split_and!; naive_solver eauto
      using is_unstamped_path2AlsoNonVars.
  - intros * Hu1 IHs1 Hus1 g.
    move: IHs1 => /(.$ g) /= [ds' [g1 ?]]; destruct_and!.
    exists (dpt (pv (vobj ds'))), g1; split_and!; cbn;
      try eapply storeless_typing.iD_Val_New; eauto 2;
      repeat constructor; eauto with f_equal.
  - intros * Hu1 Hu2 IHs2 g.
    (* Here and for standard subsumption, by stamping the subtyping
      derivation before typing, we needn't use monotonicity on [Hs],
      which holds but would require extra boilerplate. *)
    move: (stamp_obj_ident_subtyping Hu1) => /(.$ g) [g1 [Hts1 Hle1]].
    move: IHs2 => /(.$ g1) [d' [g2 [Hts2 [Hle2 Hs]]]]; lte g g1 g2.
    have [p' Heq]: ∃ p', d' = dpt p'. {
      move: Hs => {Hts2}; destruct d'; rewrite /= /from_option => -[?[??]];
        try case_match; simplify_eq; eauto 2.
    }
    exists d', g2; subst d'; split_and!; ev; eauto 3.
  Qed.

  Lemma stamp_obj_ident_typed g Γ e T: Γ u⊢ₜ e : T →
    ∃ e' g',
    Γ s⊢ₜ[ g' ] e' : T ∧ g ⊆ g' ∧ stamps_tm' (length Γ) e g' e'.
  Proof. unmut_lemma (stamp_obj_ident_typing_mut Γ). Qed.

  (** [stamps_tm'] implies [same_skel_tm], which is a bisimulation, as shown
  by [simulation_skeleton_erased_steps]. *)
  Lemma stamp_bisim_same_skel_tm {n e g e_s}:
    stamps_tm' n e g e_s → same_skel_tm e e_s.
  Proof. by case => /unstamp_same_skel_tm. Qed.

  (** * Stamping theorem 5.3. *)
  Lemma stamp_typed Γ e T g: Γ u⊢ₜ e : T →
    ∃ e' g',
    Γ v⊢ₜ[ g' ] e' : T ∧ g ⊆ g' ∧ same_skel_tm e e'.
  Proof.
    intros (e' & g' & HobjI' & ? & ?)%
      (stamp_obj_ident_typed g).
    exists e', g'; split_and! => //. exact: stamp_bisim_same_skel_tm.
  Qed.

  Lemma stamp_obj_ident_path_typed Γ g p T i: Γ u⊢ₚ p : T, i →
    ∃ g',
    Γ s⊢ₚ[ g' ] p : T, i ∧ g ⊆ g'.
  Proof. unmut_lemma (stamp_obj_ident_subtyping_mut Γ). Qed.

  Lemma stamp_path_typed Γ p T g i: Γ u⊢ₚ p : T, i →
    ∃ g',
    Γ v⊢ₚ[ g' ] p : T, i ∧ g ⊆ g'.
  Proof.
    intros (g' & HobjI' & ?)%(stamp_obj_ident_path_typed g).
    exists g'; split_and! => //.
  Qed.
End syntyping_stamping_lemmas.
