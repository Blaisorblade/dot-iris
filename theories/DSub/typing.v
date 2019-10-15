(**
  A stamped typing judgment for DSub, allowing arbitrary values in paths.
  We show that unstamped typing derivations from [D.DSubSyn.typing_objIdent] can
  be converted to stamped derivations of this typing judgment, in lemma
  [stamp_typing_mut].
*)
From D Require Import tactics.
From D.DSub Require Export syn.
From D.DSub Require Import stampingDefsCore astStamping.
From D.DSubSyn Require Import typing_objIdent.

Implicit Types (L T U V : ty) (v : vl) (e : tm) (Γ : ctx).

Section syntyping.
  Context `(hasStampTable: stampTable).
  Reserved Notation "Γ s⊢ₜ e : T" (at level 74, e, T at next level).
  Reserved Notation "Γ s⊢ₜ T1 , i1 <: T2 , i2" (at level 74, T1, T2, i1, i2 at next level).

Inductive typed Γ : tm → ty → Prop :=
| Appv_typed e1 v2 T1 T2:
    Γ s⊢ₜ e1: TAll T1 T2 →                        Γ s⊢ₜ tv v2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ s⊢ₜ tapp e1 (tv v2) : T2.|[v2/]
(** Non-dependent application; allowed for any argument. *)
| App_typed e1 e2 T1 T2:
    Γ s⊢ₜ e1: TAll T1 T2.|[ren (+1)] →      Γ s⊢ₜ e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ s⊢ₜ tapp e1 e2 : T2
| Lam_typed e T1 T2:
    (* T1 :: Γ s⊢ₜ e : T2 → (* Would work, but allows the argument to occur in its own type. *) *)
    T1.|[ren (+1)] :: Γ s⊢ₜ e : T2 →
    (*─────────────────────────*)
    Γ s⊢ₜ tv (vabs e) : TAll T1 T2
| Nat_typed n:
    Γ s⊢ₜ tv (vnat n): TNat

(** "General" rules *)
| Var_typed x T :
    (* After looking up in Γ, we must weaken T for the variables on top of x. *)
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ s⊢ₜ tv (var_vl x) : T.|[ren (+x)]
| Subs_typed e T1 T2 i :
    Γ s⊢ₜ T1, 0 <: T2, i → Γ s⊢ₜ e : T1 →
    (*───────────────────────────────*)
    Γ s⊢ₜ iterate tskip i e : T2
| Vty_abs_typed T L U σ s :
    T ~[ length Γ ] (getStampTable, (s, σ)) →
    Γ s⊢ₜ T, 1 <: U, 1 →
    Γ s⊢ₜ L, 1 <: T, 1 →
    Γ s⊢ₜ tv (vstamp σ s) : TTMem L U
(* A bit surprising this is needed, but appears in the DOT papers, and this is
   only admissible if t has a type U that is a proper subtype of TAnd T1 T2. *)
where "Γ s⊢ₜ e : T " := (typed Γ e T)
with
subtype Γ : ty → nat → ty → nat → Prop :=
| Refl_stp i T :
    Γ s⊢ₜ T, i <: T, i

| Trans_stp i1 i2 i3 T1 T2 T3:
    Γ s⊢ₜ T1, i1 <: T2, i2 → Γ s⊢ₜ T2, i2 <: T3, i3 → Γ s⊢ₜ T1, i1 <: T3, i3

(* "Structural" rules about indexes *)
| TSucc_stp T i:
    Γ s⊢ₜ T, i <: T, S i
| TMono_stp T1 T2 i:
    Γ s⊢ₜ T1, i <: T2, i →
    Γ s⊢ₜ T1, S i <: T2, S i

(* "Logical" connectives *)
| Top_stp i T :
    Γ s⊢ₜ T, i <: TTop, i
| Bot_stp i T :
    Γ s⊢ₜ TBot, i <: T, i

(* Type selections *)
| SelU_stp L U v:
    Γ s⊢ₜ tv v : TTMem L U →
    Γ s⊢ₜ TSel v, 0 <: U, 1

| LSel_stp L U v:
    Γ s⊢ₜ tv v : TTMem L U →
    Γ s⊢ₜ L, 1 <: TSel v, 0

(* "Congruence" or "variance" rules for subtyping. Unneeded for "logical" types.
 "Cov" stands for covariance, "Con" for contravariance. *)
(* Needed? Maybe drop later instead? *)
(* | TLaterCov_stp T1 T2 i:
    Γ s⊢ₜ T1, S i <: T2, S i →
    Γ s⊢ₜ TLater T1, i <: TLater T2, i *)
| TAllConCov_stp T1 T2 U1 U2 i:
    (* "Tight" premises. *)
    Γ s⊢ₜ T2, S i <: T1, S i →
    iterate TLater (S i) T2.|[ren (+1)] :: Γ s⊢ₜ U1, S i <: U2, S i →
    Γ s⊢ₜ TAll T1 U1, i <: TAll T2 U2, i
| TTMemConCov_stp L1 L2 U1 U2 i:
    Γ s⊢ₜ L2, S i <: L1, S i →
    Γ s⊢ₜ U1, S i <: U2, S i →
    Γ s⊢ₜ TTMem L1 U1, i <: TTMem L2 U2, i
where "Γ s⊢ₜ T1 , i1 <: T2 , i2" := (subtype Γ T1 i1 T2 i2).

(* Just to show this doesn't work as easily. *)
(* Lemma stamp_typing_v1 Γ:
  (∀ e T, Γ u⊢ₜ e : T → Γ s⊢ₜ e : T) ∧
  (∀ T1 i1 T2 i2, Γ u⊢ₜ T1, i1 <: T2, i2 → Γ s⊢ₜ T1, i1 <: T2, i2).
Proof.
  eapply typing_mut_ind with
      (P := λ Γ e T _, Γ s⊢ₜ e : T)
      (P0 := λ Γ T1 i1 T2 i2 _, Γ s⊢ₜ T1, i1 <: T2, i2); clear Γ;
    try solve [econstructor; eauto].
Abort. *)

Lemma Vty_typed Γ T L U σ s :
    T ~[ length Γ ] (getStampTable, (s, σ)) →
    Γ s⊢ₜ tv (vstamp σ s) : TTMem T T.
Proof. intros H. apply (Vty_abs_typed Γ T); auto using Refl_stp. Qed.
End syntyping.

Notation "Γ s⊢ₜ[ g  ] e : T" := (typed g Γ e T) (at level 74, e, T at next level).
Notation "Γ s⊢ₜ[ g  ] T1 , i1 <: T2 , i2" := (subtype g Γ T1 i1 T2 i2) (at level 74, T1, T2, i1, i2 at next level).

Scheme stamped_typed_mut_ind := Induction for typed Sort Prop
with   stamped_subtype_mut_ind := Induction for subtype Sort Prop.
Combined Scheme stamped_typing_mut_ind from stamped_typed_mut_ind, stamped_subtype_mut_ind.

Hint Constructors subtype typed : core.
Remove Hints Trans_stp : core.
Hint Extern 10 => try_once Trans_stp : core.

Lemma stamped_typing_mono_mut Γ (g g' : stys) (Hle: g ⊆ g'):
  (∀ e T, Γ s⊢ₜ[ g ] e : T → Γ s⊢ₜ[ g' ] e : T) ∧
  (∀ T1 i1 T2 i2, Γ s⊢ₜ[ g ] T1, i1 <: T2, i2 → Γ s⊢ₜ[ g' ] T1, i1 <: T2, i2).
Proof.
  eapply stamped_typing_mut_ind with
      (P := λ Γ e T _, Γ s⊢ₜ[ g' ] e : T)
      (P0 := λ Γ T1 i1 T2 i2 _, Γ s⊢ₜ[ g' ] T1, i1 <: T2, i2);
  clear Γ; intros; ev; by eauto.
Qed.
Lemma stamped_typed_mono Γ (g g' : stys) (Hle: g ⊆ g') e T:
  Γ s⊢ₜ[ g ] e : T → Γ s⊢ₜ[ g' ] e : T.
Proof. by apply (stamped_typing_mono_mut Γ g g'). Qed.
Lemma stamped_subtype_mono Γ (g g' : stys) (Hle: g ⊆ g') T1 i1 T2 i2:
  Γ s⊢ₜ[ g ] T1, i1 <: T2, i2 → Γ s⊢ₜ[ g' ] T1, i1 <: T2, i2.
Proof. by apply (stamped_typing_mono_mut Γ g g'). Qed.

Hint Extern 5 => try_once stamped_typed_mono : core.
Hint Extern 5 => try_once stamped_subtype_mono : core.

Hint Extern 5 => try_once stamps_unstamp_mono_tm : core.
Hint Extern 5 => try_once is_stamped_mono_tm : core.

Lemma stamp_typing_mut Γ :
  (∀ e T, Γ u⊢ₜ e : T → ∀ (g : stys), ∃ (e' : tm) (g' : stys),
    Γ s⊢ₜ[ g' ] e' : T ∧ g ⊆ g' ∧ stamps_tm (length Γ) e g' e') ∧
  (∀ T1 i1 T2 i2, Γ u⊢ₜ T1, i1 <: T2, i2 →
    ∀ (g : stys), ∃ (g' : stys), Γ s⊢ₜ[ g' ] T1, i1 <: T2, i2 ∧ g ⊆ g').
Proof.
  eapply typing_mut_ind with
      (P := λ Γ e T _, ∀ g, ∃ (e' : tm) (g' : stys),
      Γ s⊢ₜ[ g' ] e' : T ∧ g ⊆ g' ∧ stamps_tm (length Γ) e g' e')
      (P0 := λ Γ T1 i1 T2 i2 _, ∀ (g : stys), ∃ (g' : stys), Γ s⊢ₜ[ g' ] T1, i1 <: T2, i2 ∧ g ⊆ g'); clear Γ.
  all: try solve [intros; ev; econstructor; eauto 2].
  Local Ltac lte g g1 g2 := have ?: g ⊆ g2 by trans g1.
  (* Hint Extern 5 (_ ⊆ _) => try_once transitivity. *)
  all: try solve [intros * Hu1 IHs1 Hu2 IHs2 g;
    (* Strategy for cases of subtyping with multiple premises:
       - apply the induction hypothesis on the first premise with map [g], and obtain map [g1];
       - apply the induction hypothesis on the second premise with map [g1], and obtain map [g2];
       - exhibit map [g2]. *)
    (* Specialize IHs1 (with [/(.$ g]) and split the result. Ditto IHs2. *)
    move: IHs1 => /(.$ g) [g1 [IHs1 Hle1]];
    move: IHs2 => /(.$ g1) [g2 [IHs2 Hle2]]; ev; lte g g1 g2;
    exists g2; eauto].
  - intros * Hu1 IHs1 Hu2 IHs2 g.
    move: IHs1 => /(.$ g) [e1' [g1 [IHs1 [Hle1 ?]]]];
    move: IHs2 => /(.$ g1) [e2' [g2 [IHs2 [Hle2 [Hus1 ?]]]]]; ev.
    exists (tapp e1' (tv (var_vl x2))), g2; cbn.
    (* Expressions that appear in types must stamp to themselves! *)
    suff ?: e2' = tv (var_vl x2).
    by subst; lte g g1 g2; split_and!; eauto with f_equal.
    destruct e2' as [v'| |]; try discriminate; f_equal.
    move: Hus1 => []. exact: var_stamps_to_self1.
  - intros * Hu1 IHs1 Hu2 IHs2 g.
    move: IHs1 => /(.$ g) [e1' [g1 [IHs1 [Hle1 ?]]]];
    move: IHs2 => /(.$ g1) [e2' [g2 [IHs2 [Hle2 ?]]]]; ev.
    exists (tapp e1' e2'), g2; cbn.
    split_and!; lte g g1 g2; eauto with f_equal.
  - intros * ? Hu1 IHs1 g.
    move: IHs1 => /(.$ g) [e' [g1 [IHs1 [Hle1 ?]]]]; ev.
    exists (tv (vabs e')), g1; cbn.
    split_and!; eauto with f_equal.
  - intros. exists (tv (vnat n)), g; cbn.
    split_and!; eauto with f_equal.
  - intros. exists (tv (var_vl x)), g; cbn.
    have ? : x < length Γ. exact: lookup_lt_Some.
    split_and!; eauto with f_equal.
  - intros * ? IHs1 ? IHs2 g.
    move: IHs1 => /(.$ g) [g1 [Hts1 Hle1]].
    move: IHs2 => /(.$ g1) [e' [g2 [Hts2 [Hle2 Hs]]]].
    eapply stamps_tm_skip with (i := i) in Hs.
    exists (iterate tskip i e'), g2; lte g g1 g2; eauto.
    (* The core and most interesting case! Stamping vty! *)
  - intros * HclT ? Hu1 IHs1 Hu2 IHs2 g.
    move: IHs1 => /(.$ g) [g1 [Hts1 Hle1]].
    move: IHs2 => /(.$ g1) [g2 [Hts2 Hle2 ]].
    have Husv: is_unstamped_vl (vty T) by auto.
    destruct (extract g2 (length Γ) T) as [g3 [s σ]] eqn:Heqo.
    move: Heqo => [Heqg3 Heqs Heqσ].
    destruct (stamp_vty_spec g2 Husv HclT); ev.
    (have ?: g2 ⊆ g3 by simplify_eq); lte g g1 g2; lte g g2 g3; lte g1 g2 g3.
    exists (tv (vstamp σ s)), g3; cbn.
    simplify_eq; split_and!; eauto 4 with f_equal.
  - intros * Hu1 Hs1 g.
    move: Hs1 => /(.$ g) [g1 [Hs1 Hle1]].
    exists g1; eauto.
  - intros * Hus ? IHs1 g.
    move: IHs1 => /(.$ g) [e' [g1 [Hts1 [Hle1 [Hus1 _]]]]].
    (* Expressions that appear in types must stamp to themselves! *)
    suff ?: e' = tv v by subst; eauto.
    destruct e' as [v'| |]; try discriminate; f_equal; move: Hus1 => [].
    have [x ->]: ∃ x, v = var_vl x by inverse Hus.
    exact: var_stamps_to_self1.
  - intros * Hus ? IHs1 g.
    move: IHs1 => /(.$ g) [e' [g1 [Hts1 [Hle1 [Hus1 _]]]]].
    (* Expressions that appear in types must stamp to themselves! *)
    suff ?: e' = tv v by subst; eauto.
    destruct e' as [v'| |]; try discriminate; f_equal; move: Hus1 => [].
    have [x ->]: ∃ x, v = var_vl x by inverse Hus.
    exact: var_stamps_to_self1.
Qed.
