From D.Dot Require Import typing_objIdent stampingDefsCore astStamping.
From D.Dot Require typing_unstamped.

Set Implicit Arguments.

Section syntyping_stamping_lemmas.

  Hint Constructors typed subtype dms_typed dm_typed path_typed : core.
  Remove Hints Trans_stp : core.
  Hint Extern 10 => try_once Trans_stp : core.

  Arguments typed: clear implicits.
  Arguments dms_typed: clear implicits.
  Arguments dm_typed: clear implicits.
  Arguments path_typed: clear implicits.
  Arguments subtype: clear implicits.

  Reserved Notation "Γ |⊢ₜ[ g  ] e : T"
    (at level 74, e, T at next level).
  Reserved Notation "Γ |ds V |⊢[ g  ] ds : T"
    (at level 74, ds, T, V at next level).
  Reserved Notation "Γ |d V |⊢[ g  ]{ l := d  } : T "
    (at level 74, l, d, T, V at next level).
  Reserved Notation "Γ |⊢ₚ[ g  ] p : T , i" (at level 74, p, T, i at next level).
  Reserved Notation "Γ |⊢ₜ[ g  ] T1 , i1 <: T2 , i2" (at level 74, T1, T2, i1, i2 at next level).

  Notation "Γ |⊢ₜ[ g  ] e : T " := (typed g Γ e T).
  Notation "Γ |ds V |⊢[ g  ] ds : T" := (dms_typed g Γ V ds T).
  Notation "Γ |d V |⊢[ g  ]{ l := d  } : T" := (dm_typed g Γ V l d T).
  Notation "Γ |⊢ₚ[ g  ] p : T , i" := (path_typed g Γ p T i).
  Notation "Γ |⊢ₜ[ g  ] T1 , i1 <: T2 , i2" := (subtype g Γ T1 i1 T2 i2).

  Implicit Types (L T U V : ty) (v : vl) (e : tm) (d : dm) (p: path) (ds : dms) (Γ : list ty) (g : stys).


  Lemma stamped_objIdent_typing_mono_mut Γ (g g' : stys) (Hle: g ⊆ g'):
    (∀ e T, Γ |⊢ₜ[ g ] e : T → Γ |⊢ₜ[ g' ] e : T) ∧
    (∀ V ds T, Γ |ds V |⊢[ g ] ds : T → Γ |ds V |⊢[ g' ] ds : T) ∧
    (∀ V l d T, Γ |d V |⊢[ g ]{ l := d } : T → Γ |d V |⊢[ g' ]{ l := d } : T) ∧
    (∀ p T i, Γ |⊢ₚ[ g ] p : T, i → Γ |⊢ₚ[ g' ] p : T, i) ∧
    (∀ T1 i1 T2 i2, Γ |⊢ₜ[ g ] T1, i1 <: T2, i2 → Γ |⊢ₜ[ g' ] T1, i1 <: T2, i2).
  Proof.
    eapply stamped_objIdent_typing_mut_ind with
        (P := λ Γ e T _, Γ |⊢ₜ[ g' ] e : T)
        (P0 := λ Γ V ds T _, Γ |ds V |⊢[ g' ] ds : T)
        (P1 := λ Γ V l d T _, Γ |d V |⊢[ g' ]{ l := d } : T)
        (P2 := λ Γ p T i _, Γ |⊢ₚ[ g' ] p : T, i)
        (P3 := λ Γ T1 i1 T2 i2 _, Γ |⊢ₜ[ g' ] T1, i1 <: T2, i2);
    clear Γ; intros; naive_solver.
  Qed.
  Lemma stamped_objIdent_typed_mono Γ (g g' : stys) (Hle: g ⊆ g') e T:
    Γ |⊢ₜ[ g ] e : T → Γ |⊢ₜ[ g' ] e : T.
  Proof. by apply (@stamped_objIdent_typing_mono_mut Γ g g'). Qed.
  Lemma stamped_objIdent_subtype_mono Γ (g g' : stys) (Hle: g ⊆ g') T1 i1 T2 i2:
    Γ |⊢ₜ[ g ] T1, i1 <: T2, i2 → Γ |⊢ₜ[ g' ] T1, i1 <: T2, i2.
  Proof. by apply (@stamped_objIdent_typing_mono_mut Γ g g'). Qed.

  Lemma stamped_objIdent_dms_typed_mono Γ (g g' : stys) (Hle: g ⊆ g'):
    ∀ V ds T, Γ |ds V |⊢[ g ] ds : T → Γ |ds V |⊢[ g' ] ds : T.
  Proof. by apply (@stamped_objIdent_typing_mono_mut Γ g g'). Qed.
  Lemma stamped_objIdent_dm_typed_mono Γ (g g' : stys) (Hle: g ⊆ g'):
    ∀ V l d T, Γ |d V |⊢[ g ]{ l := d } : T → Γ |d V |⊢[ g' ]{ l := d } : T.
  Proof. by apply (@stamped_objIdent_typing_mono_mut Γ g g'). Qed.
  Lemma stamped_objIdent_path_typed_mono Γ (g g' : stys) (Hle: g ⊆ g'):
    ∀ p T i, Γ |⊢ₚ[ g ] p : T, i → Γ |⊢ₚ[ g' ] p : T, i.
  Proof. by apply (@stamped_objIdent_typing_mono_mut Γ g g'). Qed.

  Hint Extern 5 => try_once stamped_objIdent_typed_mono : core.
  Hint Extern 5 => try_once stamped_objIdent_dms_typed_mono : core.
  Hint Extern 5 => try_once stamped_objIdent_dm_typed_mono : core.
  Hint Extern 5 => try_once stamped_objIdent_path_typed_mono : core.
  Hint Extern 5 => try_once stamped_objIdent_subtype_mono : core.

  Hint Extern 5 => try_once is_stamped_mono_tm : core.
  Hint Extern 5 => try_once stamps_unstamp_mono_tm : core.
  Hint Extern 5 => try_once is_stamped_mono_dm : core.
  Hint Extern 5 => try_once stamps_unstamp_mono_dm : core.

  Hint Resolve unstamped_stamped_type var_stamps_to_self1 path_stamps_to_self1 : core.
  Hint Extern 998 (_ = _) => f_equal : core.

  Local Ltac lte g g1 g2 := have ?: g ⊆ g2 by trans g1.

  (* Importing this earlier shadows too much. *)
  Import typing_unstamped.

  Lemma stamp_objIdent_typing_mut Γ :
    (∀ e T, Γ u⊢ₜ e : T →
      ∀ (g : stys), ∃ e' (g' : stys),
      Γ |⊢ₜ[ g' ] e' : T ∧ g ⊆ g' ∧ stamps_tm (length Γ) e g' e') ∧
    (∀ V ds T, Γ |ds V u⊢ ds : T →
      ∀ (g : stys), ∃ ds' (g' : stys),
      Γ |ds V |⊢[ g' ] ds' : T ∧ g ⊆ g' ∧ stamps_dms (S (length Γ)) ds g' ds') ∧
    (∀ V l d T, Γ |d V u⊢{ l := d } : T →
      ∀ (g : stys), ∃ d' (g' : stys),
      Γ |d V |⊢[ g' ]{ l := d' } : T
        ∧ g ⊆ g' ∧ stamps_dm (S (length Γ)) d g' d') ∧
    (∀ p T i, Γ u⊢ₚ p : T, i →
      ∀ (g : stys), ∃ p' (g' : stys),
      Γ |⊢ₚ[ g' ] p' : T, i
        ∧ g ⊆ g' ∧ stamps_path (length Γ) p g' p') ∧
    (∀ T1 i1 T2 i2, Γ u⊢ₜ T1, i1 <: T2, i2 →
      ∀ (g : stys), ∃ (g' : stys), Γ |⊢ₜ[ g' ] T1, i1 <: T2, i2 ∧ g ⊆ g').
  Proof.
    eapply unstamped_typing_mut_ind with
      (P := λ Γ e T _, ∀ g, ∃ e' (g' : stys),
        Γ |⊢ₜ[ g' ] e' : T ∧ g ⊆ g' ∧ stamps_tm (length Γ) e g' e')
      (P0 := λ Γ V ds T _, ∀ g, ∃ ds' (g' : stys),
        Γ |ds V |⊢[ g' ] ds' : T ∧ g ⊆ g' ∧ stamps_dms (S (length Γ)) ds g' ds')
      (P1 := λ Γ V l d T _, ∀ (g : stys), ∃ d' (g' : stys),
        Γ |d V |⊢[ g' ]{ l := d' } : T ∧ g ⊆ g' ∧
        stamps_dm (S (length Γ)) d g' d')
      (P2 := λ Γ p T i _, ∀ (g : stys), ∃ p' (g' : stys),
        Γ |⊢ₚ[ g' ] p' : T, i ∧ g ⊆ g' ∧ stamps_path (length Γ) p g' p')
      (P3 := λ Γ T1 i1 T2 i2 _, ∀ (g : stys), ∃ (g' : stys),
        Γ |⊢ₜ[ g' ] T1, i1 <: T2, i2 ∧ g ⊆ g');
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
  - intros * Hus1 Hcl Hu1 IHs1 g.
    move: IHs1 => /(.$ g) [e' [g1 ?]].
    exists (tv (vabs e')), g1. naive_solver.
  - intros * Huds1 IHs1 Hus1 Hcl g.
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
  - intros * Hu1 IHs1 Hu2 IHs2 g.
    move: IHs1 => /(.$ g) [e1' [g1 ?]];
    move: IHs2 => /(.$ g1) [e2' [g2 ?]]; ev; lte g g1 g2.
    exists (tv (var_vl x)), g2.
    suff [? ?]: e1' = tv (var_vl x) ∧ e2' = tv (var_vl x) by naive_solver.
    split; [destruct e1'| destruct e2']; naive_solver.
  - intros; exists [], g; naive_solver.
  - intros * Hu1 IHs1 Hu2 IHs2 ? g.
    move: IHs1 => /(.$ g) [d' [g1 ?]].
    move: IHs2 => /(.$ g1) [ds' [g2 ?]]; ev; lte g g1 g2.
    have ?: unstamp_dm g2 d' = d by naive_solver.
    exists ((l, d') :: ds'), g2; cbn.
    split_and!; eauto 4 using unstamp_dms_hasnt.

    (* The core and most interesting case! Stamping dtysyn! *)
  - intros * HclT Hus Hu1 IHs1 Hu2 IHs2 g.
    move: IHs1 => /(.$ g) [g1 [Hts1 Hle1]];
    move: IHs2 => /(.$ g1) [g2 [Hts2 Hle2 ]].
    have Husv: is_unstamped_dm (dtysyn T) by auto.
    destruct (extract g2 (S (length Γ)) T) as [g3 [s σ]] eqn:Heqo.
    move: Heqo => [Heqg3 Heqs Heqσ].
    have {Heqσ} -Heqσ: σ = idsσ (S (length Γ)) by naive_solver.
    destruct (stamp_dtysyn_spec g2 Husv HclT); destruct_and!.
    have ?: g2 ⊆ g3 by simplify_eq. lte g g1 g2; lte g g2 g3; lte g1 g2 g3.
    exists (dtysem σ s), g3; simplify_eq; split_and!;
      first eapply (typing_objIdent.dty_typed _ T); auto 2; [
        exact: (stamped_objIdent_subtype_mono _ Hts1)|
        exact: (stamped_objIdent_subtype_mono _ Hts2)].
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) /= [e1' [g1 ?]]; destruct_and!.
    have [v' ?]: ∃ v', e1' = tv v' by destruct e1'; naive_solver.
    simplify_eq/=; with_is_stamped inverse; with_is_unstamped inverse.
    exists (dvl v'), g1; naive_solver.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) /= [e1' [g1 ?]]; ev.
    destruct e1' as [v'| | |] => //. with_is_stamped inverse.
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
    split_and! => //. eapply typing_objIdent.p_subs_typed, IHs2.
    by eapply stamped_objIdent_subtype_mono, Hs1.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) /= [p1' [g1 ?]]; ev.
    exists g1. suff ?: p1' = p by naive_solver.
    move: (unstamped_path_root_is_var Hu1). naive_solver.
  - intros * Hu1 IHs1 g.
    move: IHs1 => /(.$ g) /= [p1' [g1 ?]]; ev.
    exists g1. suff ?: p1' = p by naive_solver.
    move: (unstamped_path_root_is_var Hu1). naive_solver.
  - intros * Hu1 IHs1 Hu2 IHs2 Hus2 Hcl g.
    move: IHs1 => /(.$ g) [g1 ?].
    move: IHs2 => /(.$ g1) [g2 ?]; ev; lte g g1 g2.
    exists g2; eauto.
  Qed.

  Lemma stamp_objIdent_typed Γ e T: Γ u⊢ₜ e : T →
    ∀ (g : stys), ∃ e' (g' : stys),
    Γ |⊢ₜ[ g' ] e' : T ∧ g ⊆ g' ∧ stamps_tm (length Γ) e g' e'.
  Proof. apply (stamp_objIdent_typing_mut Γ). Qed.

  Arguments typing.typed: clear implicits.
  Notation "Γ ⊢ₜ[ g  ] e : T" := (typing.typed g Γ e T)
    (at level 74, e, T at next level).

  Lemma stamp_typed Γ e T: Γ u⊢ₜ e : T →
    ∃ e' (g : stys),
    Γ ⊢ₜ[ g ] e' : T ∧ stamps_tm (length Γ) e g e'.
  Proof.
    move => /stamp_objIdent_typed HobjI.
    case (HobjI ∅) as (e' & g' & HobjI'%typing_obj_ident_to_typing & ? & ?).
    by exists e', g'.
  Qed.
End syntyping_stamping_lemmas.
