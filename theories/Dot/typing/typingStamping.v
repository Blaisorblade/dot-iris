From D.Dot Require Import typing_stamped stampingDefsCore astStamping skeleton
  path_repl_lemmas.
From D.Dot Require typing_unstamped.

Set Implicit Arguments.

Section syntyping_stamping_lemmas.

  Import typing_unstamped typing_storeless.

  Hint Constructors typing_stamped.typed typing_stamped.subtype typing_stamped.dms_typed typing_stamped.dm_typed typing_stamped.path_typed : core.
  Remove Hints typing_stamped.Trans_stp : core.
  Hint Extern 10 => try_once typing_stamped.Trans_stp : core.

  Implicit Types (L T U V : ty) (v : vl) (e : tm) (d : dm) (p: path) (ds : dms) (Γ : list ty) (g : stys).

  Hint Extern 5 (is_stamped_path _ _ _) => try_once is_stamped_mono_path : core.

  Lemma stamped_objIdent_typing_mono_mut Γ g :
    (∀ e T, Γ s⊢ₜ[ g ] e : T → ∀ g' (Hle : g ⊆ g'), Γ s⊢ₜ[ g' ] e : T) ∧
    (∀ V ds T, Γ |ds V s⊢[ g ] ds : T → ∀ g' (Hle : g ⊆ g'), Γ |ds V s⊢[ g' ] ds : T) ∧
    (∀ V l d T, Γ |d V s⊢[ g ]{ l := d } : T → ∀ g' (Hle : g ⊆ g'), Γ |d V s⊢[ g' ]{ l := d } : T) ∧
    (∀ p T i, Γ s⊢ₚ[ g ] p : T, i → ∀ g' (Hle : g ⊆ g'), Γ s⊢ₚ[ g' ] p : T, i) ∧
    (∀ T1 i1 T2 i2, Γ s⊢ₜ[ g ] T1, i1 <: T2, i2 → ∀ g' (Hle : g ⊆ g'), Γ s⊢ₜ[ g' ] T1, i1 <: T2, i2).
  Proof.
    eapply stamped_objIdent_typing_mut_ind with
        (P := λ Γ g e T _, ∀ g' (Hle : g ⊆ g'), Γ s⊢ₜ[ g' ] e : T)
        (P0 := λ Γ g V ds T _, ∀ g' (Hle : g ⊆ g'), Γ |ds V s⊢[ g' ] ds : T)
        (P1 := λ Γ g V l d T _, ∀ g' (Hle : g ⊆ g'), Γ |d V s⊢[ g' ]{ l := d } : T)
        (P2 := λ Γ g p T i _, ∀ g' (Hle : g ⊆ g'), Γ s⊢ₚ[ g' ] p : T, i)
        (P3 := λ Γ g T1 i1 T2 i2 _, ∀ g' (Hle : g ⊆ g'), Γ s⊢ₜ[ g' ] T1, i1 <: T2, i2);
    clear Γ g; intros;
      repeat match goal with
      | H : forall g : stys, _ |- _ => specialize (H g' Hle)
      end; eauto.
  Qed.
  Lemma stamped_objIdent_typed_mono Γ (g g' : stys) (Hle: g ⊆ g') e T:
    Γ s⊢ₜ[ g ] e : T → Γ s⊢ₜ[ g' ] e : T.
  Proof. unmut_lemma (stamped_objIdent_typing_mono_mut Γ g). Qed.
  Lemma stamped_objIdent_subtype_mono Γ (g g' : stys) (Hle: g ⊆ g') T1 i1 T2 i2:
    Γ s⊢ₜ[ g ] T1, i1 <: T2, i2 → Γ s⊢ₜ[ g' ] T1, i1 <: T2, i2.
  Proof. unmut_lemma (stamped_objIdent_typing_mono_mut Γ g). Qed.

  Lemma stamped_objIdent_dms_typed_mono Γ (g g' : stys) (Hle: g ⊆ g'):
    ∀ V ds T, Γ |ds V s⊢[ g ] ds : T → Γ |ds V s⊢[ g' ] ds : T.
  Proof. unmut_lemma (stamped_objIdent_typing_mono_mut Γ g). Qed.
  Lemma stamped_objIdent_dm_typed_mono Γ (g g' : stys) (Hle: g ⊆ g'):
    ∀ V l d T, Γ |d V s⊢[ g ]{ l := d } : T → Γ |d V s⊢[ g' ]{ l := d } : T.
  Proof. unmut_lemma (stamped_objIdent_typing_mono_mut Γ g). Qed.
  Lemma stamped_objIdent_path_typed_mono Γ (g g' : stys) (Hle: g ⊆ g'):
    ∀ p T i, Γ s⊢ₚ[ g ] p : T, i → Γ s⊢ₚ[ g' ] p : T, i.
  Proof. unmut_lemma (stamped_objIdent_typing_mono_mut Γ g). Qed.

  Hint Extern 5 => try_once stamped_objIdent_typed_mono : core.
  Hint Extern 5 => try_once stamped_objIdent_dms_typed_mono : core.
  Hint Extern 5 => try_once stamped_objIdent_dm_typed_mono : core.
  Hint Extern 5 => try_once stamped_objIdent_path_typed_mono : core.
  Hint Extern 5 => try_once stamped_objIdent_subtype_mono : core.

  Hint Extern 5 => try_once is_stamped_mono_tm : core.
  Hint Extern 5 => try_once stamps_unstamp_mono_tm : core.
  Hint Extern 5 => try_once is_stamped_mono_dm : core.
  Hint Extern 5 => try_once stamps_unstamp_mono_dm : core.
  (* Hint Extern 5 => try_once stamps_unstamp_mono_vl : core. *)

  Hint Resolve unstamped_stamped_type var_stamps_to_self1 path_stamps_to_self1 : core.
  Hint Extern 998 (_ = _) => f_equal : core.

  Local Ltac lte g g1 g2 := have ?: g ⊆ g2 by trans g1.

  Hint Resolve is_stamped_path2tm is_unstamped_path2tm unstamp_path2tm : core.
  Hint Resolve unstamped_stamped_path unstamped_stamps_self_path : core.

  Hint Resolve psubst_one_implies is_unstamped_ty_subst : core.
  (** These hints slow down proof search. *)
  (** Not directed. *)
  Remove Hints typing_stamped.psingleton_trans : core.
  (** These cause cycles. *)
  Remove Hints typing_stamped.p_mu_e_typed : core.
  Remove Hints typing_stamped.p_mu_i_typed : core.

  Lemma stamp_objIdent_typing_mut Γ :
    (∀ e T, Γ u⊢ₜ e : T →
      ∀ (g : stys), ∃ e' (g' : stys),
      Γ s⊢ₜ[ g' ] e' : T ∧ g ⊆ g' ∧ stamps_tm (length Γ) e g' e') ∧
    (∀ V ds T, Γ |ds V u⊢ ds : T →
      ∀ (g : stys), ∃ ds' (g' : stys),
      Γ |ds V s⊢[ g' ] ds' : T ∧ g ⊆ g' ∧ stamps_dms (S (length Γ)) ds g' ds') ∧
    (∀ V l d T, Γ |d V u⊢{ l := d } : T →
      ∀ (g : stys), ∃ d' (g' : stys),
      Γ |d V s⊢[ g' ]{ l := d' } : T
        ∧ g ⊆ g' ∧ stamps_dm (S (length Γ)) d g' d') ∧
    (∀ p T i, Γ u⊢ₚ p : T, i →
      ∀ (g : stys), ∃ p' (g' : stys),
      Γ s⊢ₚ[ g' ] p' : T, i
        ∧ g ⊆ g' ∧ stamps_path (length Γ) p g' p') ∧
    (∀ T1 i1 T2 i2, Γ u⊢ₜ T1, i1 <: T2, i2 →
      ∀ (g : stys), ∃ (g' : stys), Γ s⊢ₜ[ g' ] T1, i1 <: T2, i2 ∧ g ⊆ g').
  Proof.
    eapply unstamped_typing_mut_ind with
      (P := λ Γ e T _, ∀ g, ∃ e' (g' : stys),
        Γ s⊢ₜ[ g' ] e' : T ∧ g ⊆ g' ∧ stamps_tm (length Γ) e g' e')
      (P0 := λ Γ V ds T _, ∀ g, ∃ ds' (g' : stys),
        Γ |ds V s⊢[ g' ] ds' : T ∧ g ⊆ g' ∧ stamps_dms (S (length Γ)) ds g' ds')
      (P1 := λ Γ V l d T _, ∀ (g : stys), ∃ d' (g' : stys),
        Γ |d V s⊢[ g' ]{ l := d' } : T ∧ g ⊆ g' ∧
        stamps_dm (S (length Γ)) d g' d')
      (P2 := λ Γ p T i _, ∀ (g : stys), ∃ p' (g' : stys),
        Γ s⊢ₚ[ g' ] p' : T, i ∧ g ⊆ g' ∧ stamps_path (length Γ) p g' p')
      (P3 := λ Γ T1 i1 T2 i2 _, ∀ (g : stys), ∃ (g' : stys),
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
      exists g2; split_and!; eauto 3].
    all: try solve [intros * Hu1 IHs1 **; move: IHs1 => /(.$ g) [g1 [Hts1 Hle1]]; exists g1; split_and!; eauto 3].
    all: try solve [intros; exists g; split_and!; auto 3].

  - intros * Hu1 IHs1 Hu2 IHs2 g.
    move: IHs1 => /(.$ g) [e1' [g1 ?]];
    move: IHs2 => /(.$ g1) [e2' [g2 ?]]; ev; lte g g1 g2.
    exists (tapp e1' (tv (var_vl x2))), g2.
    (* Expressions that appear in types must stamp to themselves! *)
    suff ?: e2' = tv (var_vl x2) by naive_solver.
    destruct e2'; naive_solver.
  - intros * Hus1 Husp Hu1 IHs1 Hu2 IHs2 g.
    move: IHs1 => /(.$ g) [e1' [g1 [IHs1 [Hle1 Hse1]]]];
    move: IHs2 => /(.$ g1) [p2' [g2 [IHs2 [Hle2 ?]]]]; lte g g1 g2.
    have Hse1': unstamp_tm g2 e1' = e1. by eapply stamps_unstamp_mono_tm, Hse1.
    have ?: p2' = p2. move: (unstamped_path_root_is_var Hu2). naive_solver.
    subst p2'.
    exists (tapp e1' (path2tm p2)), g2.
    (* have ?: T2 .Tp[ p2 /]~ psubst_one_ty T2 p2 by exact: psubst_one_implies.
    have ?: is_unstamped_ty (length Γ) (psubst_one_ty T2 p2)
      by eapply is_unstamped_ty_subst. *)
    split_and!; first eapply typing_stamped.App_path_typed; naive_solver eauto 4.
  - intros * Hu1 IHs1 Hu2 IHs2 g.
    move: IHs1 => /(.$ g) [e1' [g1 ?]];
    move: IHs2 => /(.$ g1) [e2' [g2 ?]]; ev; lte g g1 g2.
    exists (tapp e1' e2'), g2; naive_solver.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) [e1' [g1 ?]].
    exists (tproj e1' l), g1; naive_solver.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) [e1' [g1 ?]].
    exists (tv (var_vl x)), g1.
    suff ?: e1' = tv (var_vl x) by naive_solver.
    destruct e1'; naive_solver.
  - intros * Hus1 Hu1 IHs1 g.
    move: IHs1 => /(.$ g) [e' [g1 ?]].
    exists (tv (vabs e')), g1. naive_solver.
  - intros * Huds1 IHs1 Hus1 g.
    move: IHs1 => /(.$ g) [ds' [g1 ?]].
    exists (tv (vobj ds')), g1; naive_solver.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) [e1' [g1 ?]].
    exists (tv (var_vl x)), g1.
    suff ?: e1' = tv (var_vl x) by naive_solver.
    destruct e1'; naive_solver.
  - intros. exists (tv (vnat n)), g; naive_solver.
  - intros.
    have ? : x < length Γ by exact: lookup_lt_Some.
    exists (tv (var_vl x)), g; naive_solver.
  - intros * ? IHs1 ? IHs2 g.
    move: IHs1 => /(.$ g) [g1 [Hts1 Hle1]].
    move: IHs2 => /(.$ g1) [e' [g2 [Hts2 [Hle2 Hs]]]]; lte g g1 g2.
    eapply stamps_tm_skip with (i := i) in Hs.
    exists (iterate tskip i e'), g2; eauto.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) /= [p1' [g1 ?]]; ev.
    exists (path2tm p1'), g1; naive_solver.
  - intros; exists [], g; naive_solver.
  - intros * Hu1 IHs1 Hu2 IHs2 ? g.
    move: IHs1 => /(.$ g) [d' [g1 ?]].
    move: IHs2 => /(.$ g1) [ds' [g2 ?]]; ev; lte g g1 g2.
    have ?: unstamp_dm g2 d' = d by naive_solver.
    exists ((l, d') :: ds'), g2; cbn.
    split_and!; eauto 4 using unstamp_dms_hasnt.

    (* The core and most interesting case! Stamping dtysyn! *)
  - intros * Hus Hu1 IHs1 Hu2 IHs2 g.
    move: IHs1 => /(.$ g) [g1 [Hts1 Hle1]];
    move: IHs2 => /(.$ g1) [g2 [Hts2 Hle2]].
    have Husv: is_unstamped_dm (S (length Γ)) (dtysyn T) by auto.
    destruct (extract g2 (S (length Γ)) T) as [g3 [s σ]] eqn:Heqo.
    move: Heqo => [Heqg3 Heqs Heqσ].
    have {Heqσ} -Heqσ: σ = idsσ (S (length Γ)) by naive_solver.
    destruct (stamp_dtysyn_spec g2 Husv); destruct_and!.
    have ?: g2 ⊆ g3 by simplify_eq. lte g g1 g2; lte g g2 g3; lte g1 g2 g3.
    exists (dtysem σ s), g3; simplify_eq; split_and!;
      first eapply (typing_stamped.dty_typed _ _ T); auto 2; [
        exact: (stamped_objIdent_subtype_mono _ Hts1)|
        exact: (stamped_objIdent_subtype_mono _ Hts2)].
  - intros * Hus1 Hu1 IHs1 g.
    move: IHs1 => /(.$ g) /= [e1' [g1 ?]]; destruct_and!.
    exists (dvl (vabs e1')), g1; naive_solver.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) /= [e1' [g1 ?]]; destruct_and!.
    have [v' ?]: ∃ v', e1' = tv v' by destruct e1'; naive_solver.
    simplify_eq/=; with_is_stamped inverse; with_is_unstamped inverse.
    exists (dvl v'), g1; naive_solver.
  - intros * Hu1 IHs1 Hu2 IHs2 g.
    (* Here and for standard subsumption, by stamping the subtyping
      derivation before typing, we needn't use monotonicity on [Hs],
      which holds but would require extra boilerplate. *)
    move: IHs1 => /(.$ g) [g1 [Hts1 Hle1]].
    move: IHs2 => /(.$ g1) [d' [g2 [Hts2 [Hle2 Hs]]]]; lte g g1 g2.
    have [v' Heq]: ∃ v', d' = dvl v'. {
      move => {Hts2}.
      move: Hs.
      destruct d'; rewrite /= /from_option => -[?[??]];
        try case_match; simplify_eq; eauto 2.
    }
    exists d', g2; subst d'; split_and!; ev; eauto 3.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) /= [e1' [g1 ?]]; ev.
    destruct e1' as [v'| | | | | |] => //. with_is_stamped inverse.
    with_is_unstamped inverse.
    exists (pv (var_vl x)), g1.
    have ?: v' = var_vl x; naive_solver.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) /= [p1' [g1 ?]].
    exists p1', g1; naive_solver.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) /= [p1' [g1 ?]].
    exists (pself p1' l), g1; naive_solver.
  - intros * Hu1 IHs1 Hu2 IHs2 g.
    move: IHs1 => /(.$ g) [g1 [Hs1 ?]].
    move: IHs2 => /(.$ g1) [p1' [g2 [IHs2 ?]]]; ev; lte g g1 g2.
    exists p1', g2.
    split_and! => //. eapply typing_stamped.p_subs_typed, IHs2.
    by eapply stamped_objIdent_subtype_mono, Hs1.
  - intros * Hus Hu1 IHs1 g.
    move: IHs1 => /(.$ g) /= [p1' [g1 ?]]; ev.
    exists p1', g1.
    suff ?: p1' = p by split_and! => //; econstructor; naive_solver.
    move: (unstamped_path_root_is_var Hu1). naive_solver.
  - intros * Hus1 Hu1 IHs1 g.
    move: IHs1 => /(.$ g) /= [p1' [g1 [IHs1 ?]]]; ev.
    exists p1', g1.
    suff ?: p1' = p by split_and! => //; econstructor; naive_solver.
    move: (unstamped_path_root_is_var Hu1). naive_solver.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) /= [p1' [g1 [IHs1 ?]]]; ev.
    move: (unstamped_path_root_is_var Hu1) => Hp.
    have ?: p1' = pself p l by naive_solver; subst p1'.
    with_is_unstamped inverse; with_is_stamped inverse.
    exists p, g1. naive_solver.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) [p1' [g1 ?]]; ev.
    exists p1', g1. move: (unstamped_path_root_is_var Hu1) => ?.
    suff: p1' = p; naive_solver.
  - intros * Hu1 IHs1 Hus1 g.
    move: IHs1 => /(.$ g) [p1' [g1 ?]]; ev.
    exists q, g1. move: (unstamped_path_root_is_var Hu1) => ?.
    have ?: p1' = p by naive_solver.
    split_and!; first eapply typing_stamped.psingleton_inv_typed; naive_solver.
  - intros * Hu1 IHs1 Hu2 IHs2 g.
    move: IHs1 => /(.$ g) [p1' [g1 ?]];
    move: IHs2 => /(.$ g1) [q1' [g2 ?]]; ev; lte g g1 g2.
    move: (unstamped_path_root_is_var Hu1) => Hp1.
    move: (unstamped_path_root_is_var Hu2) => Hp2.
    have [? ?]: p1' = p ∧ q1' = q by [naive_solver]; subst p1' q1'.
    exists p, g2; split_and!;
      first eapply typing_stamped.psingleton_trans; eauto 2.
  - intros * Hu1 IHs1 Hu2 IHs2 g.
    move: IHs1 => /(.$ g) [p1' [g1 ?]];
    move: IHs2 => /(.$ g1) [ql1' [g2 ?]]; ev; lte g g1 g2.
    move: (unstamped_path_root_is_var Hu1) => Hp1.
    move: (unstamped_path_root_is_var Hu2) => Hp2.
    have [??]: p1' = p ∧ ql1' = pself q l by [naive_solver]; subst p1' ql1'.
    exists (pself p l), g2; split_and!;
      first eapply typing_stamped.psingleton_elim;
      first apply (stamped_objIdent_path_typed_mono (g := g1)); eauto 3.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) /= [p1' [g1 ?]]; ev.
    exists g1. suff ?: p1' = p by naive_solver.
    move: (unstamped_path_root_is_var Hu1). naive_solver.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) /= [p1' [g1 ?]]; ev.
    exists g1. suff ?: p1' = p by naive_solver.
    move: (unstamped_path_root_is_var Hu1). naive_solver.
  - intros * Hps Hus1 Hus2 Hu1 IHs1 g.
    move: IHs1 => /(.$ g) [p1' [g1 ?]]; ev.
    move: (unstamped_path_root_is_var Hu1) => Hp1.
    have ?: p1' = p by [naive_solver]; subst p1'.
    exists g1. repeat constructor => //.
    eapply typing_stamped.PSub_singleton_stp; eauto 2.
  - intros * Hu1 IHs1 Hu2 IHs2 g.
    move: IHs1 => /(.$ g) [p1' [g1 ?]].
    move: IHs2 => /(.$ g1) [g2 ?]; ev; lte g g1 g2.
    move: (unstamped_path_root_is_var Hu1) => Hp1.
    have ?: p1' = p by [naive_solver]; subst p1'.
    exists g2; split_and! => //.
    by apply (typing_stamped.PSym_singleton_stp _ _ T); eauto 2.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) [p1' [g1 ?]]; ev.
    move: (unstamped_path_root_is_var Hu1) => Hp1.
    have ?: p1' = p by [naive_solver]; subst p1'.
    exists g1; split_and! => //.
    by apply typing_stamped.PSelf_singleton_stp.
  - intros * Hu1 IHs1 Hu2 IHs2 Hus g.
    move: IHs1 => /(.$ g) [g1 [Hts1 Hle1]];
    move: IHs2 => /(.$ g1) [g2 [Hts2 Hle2]]; lte g g1 g2.
    exists g2; split_and! => //.
    apply typing_stamped.TAllConCov_stp; eauto 2.
  Qed.

  Lemma stamp_objIdent_typed Γ e T: Γ u⊢ₜ e : T →
    ∀ (g : stys), ∃ e' (g' : stys),
    Γ s⊢ₜ[ g' ] e' : T ∧ g ⊆ g' ∧ stamps_tm (length Γ) e g' e'.
  Proof. apply (stamp_objIdent_typing_mut Γ). Qed.

  Lemma stamp_objIdent_path_typed Γ p T i: Γ u⊢ₚ p : T, i →
    ∀ (g : stys), ∃ p' (g' : stys),
    Γ s⊢ₚ[ g' ] p' : T, i ∧ g ⊆ g' ∧ stamps_path (length Γ) p g' p'.
  Proof. apply (stamp_objIdent_typing_mut Γ). Qed.

  Lemma safe_stamp {n e g e_s}:
    stamps_tm n e g e_s → safe e_s → safe e.
  Proof. move => [/unstamp_same_skel_tm Hs _] Hsafe. exact: safe_same_skel. Qed.

  Lemma terminates_stamp {n e g e_s}:
    stamps_tm n e g e_s → terminates e_s → terminates e.
  Proof. move => [/unstamp_same_skel_tm Hs _] Hsafe. exact: terminates_same_skel. Qed.

  Lemma stamp_typed Γ e T: Γ u⊢ₜ e : T →
    ∃ e' (g : stys),
    Γ v⊢ₜ[ g ] e' : T ∧ (safe e' → safe e).
  Proof.
    move => /stamp_objIdent_typed HobjI.
    case (HobjI ∅) as (e' & g' & HobjI'%typing_obj_ident_to_typing & ? & ?).
    exists e', g'; split; first done. exact: safe_stamp.
  Qed.

  Lemma stamps_path2tm n p g p' :
    stamps_path n p g p' → stamps_tm n (path2tm p) g (path2tm p').
  Proof.
    intros; destruct_and!; induction p; destruct p'; with_is_stamped inverse;
      with_is_unstamped inverse; split_and! => //; eauto.
  Qed.

  Lemma stamp_path_typed Γ p T i: Γ u⊢ₚ p : T, i →
    ∃ p' (g : stys),
    Γ v⊢ₚ[ g ] p' : T, i ∧ (terminates (path2tm p') → terminates (path2tm p)).
  Proof.
    move => /stamp_objIdent_path_typed HobjI.
    case (HobjI ∅) as (p' & g' & HobjI'%typing_obj_ident_to_typing_mut & ? & ?).
    exists p', g'; split; first done.
    by eapply terminates_stamp, stamps_path2tm.
  Qed.
End syntyping_stamping_lemmas.
