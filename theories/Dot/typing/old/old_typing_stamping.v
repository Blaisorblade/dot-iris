(** * Stamping theorem. *)
From D Require Import prelude iris_extra.det_reduction.
From D.Dot Require Import syn core_stamping_defs.
From D.Dot Require old_unstamped_typing old_subtyping.
From D.Dot Require Import unstampedness_binding.

Set Implicit Arguments.

Set Suggest Proof Using.
Set Default Proof Using "Type".

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
  Import old_unstamped_typing.

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

  Lemma is_unstamped_ren_ty_1 i T b:
    is_unstamped_ty i b T →
    is_unstamped_ty (S i) b (shift T).
  Proof. intros Ht. eapply is_unstamped_sub_ren_ty, Ht. auto. Qed.

  (* XXX TODO remove these hints elsewhere as well? *)
  (** These hints slow down proof search. *)
  (** Not directed. *)
  Remove Hints old_subtyping.iP_Sngl_Trans : core.
  (** These cause cycles. *)
  Remove Hints old_subtyping.iP_Mu_E : core.
  Remove Hints old_subtyping.iP_Mu_I : core.
End syntyping_stamping_lemmas.
