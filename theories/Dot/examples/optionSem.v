From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot.typing Require Import typing_unstamped typing_unstamped_derived.
From D.Dot.examples Require Import typingExInfra exampleInfra hoas scalaLib.
Import DBNotation.

From iris.proofmode Require Import tactics.

From D.Dot Require Import unary_lr
  lr_lemmas lr_lemmasNoBinding lr_lemmasDefs fundamental.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Set Suggest Proof Using.
Set Default Proof Using "Type".

Import typingStamping.
Import stamp_transfer swap_later_impl.
Import astStamping dlang adequacy dlang_adequacy.
Import typing_storeless.

Import traversals.Trav1.
Import stampingDefsCore.

Lemma exist2_proper {A B : Type} (P Q : A → B → Prop):
  (∀ x y, P x y → Q x y) → (∃ x y, P x y) → (∃ x y, Q x y).
Proof. intros; ev; eauto. Qed.

(* Lemma exist2_split2 {A B : Type} (P1 : A → Prop) (P2 : B → Prop) (Q : A → B → Prop):
  (∀ x y, P1 x → P2 y → Q x y) →
  (∃ x, P1 x) →
  (∃ y, P2 y) →
  ∃ x y, Q x y.
Proof. intros; ev; eauto. Qed. *)

Lemma exist2_split2_ax {A B : Type} (P1 Q : A → B → Prop) P2:
  (∀ x y, P1 x y → P2 → Q x y) →
  (∃ x y, P1 x y) →
  P2 →
  ∃ x y, Q x y.
Proof. intros; ev; eauto. Qed.

(* Lemma drop_exists `{Inhabited A} (P : Prop): P → ∃ (x : A), P.
Proof. by intros; exists inhabitant. Qed. *)

Ltac under_f_equal :=
  let H := fresh "H" in
  eapply exist2_proper; [by intros x y H; f_equal; apply H | cbn ].

Ltac splitV := progress (
  unfold from_option in *;
  try (case_match; simplify_eq/=);
  match goal with
  | |- ∃ _ _, _ = dtysem _ _ => idtac
  | |- ∃ _ _, ?a = _ => destruct a; simplify_eq/=;
    try nosplit with_is_stamped ltac:(fun H => inversion_clear H);
    try under_f_equal
  | |- ?a = _ => destruct a; simplify_eq/=;
    try nosplit with_is_stamped ltac:(fun H => inversion_clear H);
    repeat f_equal
  end).

Section ex.
  Context `{!dlangG Σ} `{!SwapPropI Σ}.

  Goal noneV = ν {@ type "T" = ⊥ ;
          val "isEmpty" = vabs (tv (vabs (tv (vabs (tv x1)))));
          val "pmatch" = vabs (tv (vabs (tv (vabs (tv x1)))))}%dms. done.

  Lemma foo1 none' n g :
    is_stamped_tm n g none' →
    unstamp_tm g none' = tv noneV →
    ∃ σ s,
    none' = tv (ν {@ type "T" = (σ; s) ;
          val "isEmpty" = vabs (tv (vabs (tv (vabs (tv x1)))));
          val "pmatch" = vabs (tv (vabs (tv (vabs (tv x1)))))}%dms).
  Proof.
    set V := noneV.
    cbv in V; rewrite {}/V => Hs Heq.
    do 2 splitV.
    destruct l; simplify_eq.
    eapply exist2_split2_ax;
      [by intros x y H1 H2; f_equal; [apply H1 | apply H2] | cbn..]; repeat splitV.
    (* under_f_equal.
    eapply exist2_split2_ax.
      intros x y H1 H2; f_equal.
      apply H1.
      [apply H1 | apply H2] | cbn..].
    splitV.

    (* lazymatch goal with
    | |- ∃ _ _, ?c _ _ = ?c' _ _ => unify c c'; idtac c c'
    end. *)

    (* eapply exist2_split2;
      [ by intros x y H1 H2; f_equal; [apply H1 | apply H2] | cbn..]. *)
    Search _ (?P → ∃ _, ?P).
    all: repeat try apply drop_exists.
    Lemma exist_foo
    apply exist
    Ltac under_f_equal2 := eapply exist2_proper; [by intros x y H; f_equal; apply H | cbn ].
(* ?c ?a1 ?a2 = ?c' ?b1 ?b2  *)
    eapply exist2_proper.
    intros x y H.
    f_equal.
    apply H.
    splitV.
    do 5 splitV.
    splitV.

    rewrite base.exist_proper.
    f_equiv.
    simplify_eq/=.
      (* | |- ?a = _ => destruct a; simplify_eq/=; try nosplit with_is_stamped inverse; repeat f_equal end. *)
    repeat splitV. *)
    (* do 2 with_is_stamped ltac:(fun H => inversion_clear H). *)
    cbn [upS is_stamped_trav] in *.
    match goal with
    | H : Forall (is_stamped_dm _ _) _ |- _ => inversion_clear H
    end.

    destruct d; eauto;
      unfold from_option in *; with_is_stamped inverse; cbn in *; ev; simplify_eq/= => //.
  Qed.
    (* eauto.
    case_match; simplify_eq/=.

    unfold from_option in *; simplify_eq.
    rewrite /from_option
    cbn in H0.
    skip.
  Qed. *)
    (* do 2 splitV.
    unfold from_option in *. case_match. simplify_eq.
    splitV.
    splitV.
    do 2 splitV.
    case_match.

    destruct none' as [ [ | | | ds ]| | | ]; simplify_eq/=.
    destruct ds as [| d1 [| d2 ds]]; simplify_eq/=.
    repeat f_equal.
    (* destruct none' as [v'| | | ]; simplify_eq/=.
    destruct v' as [| | | ds ]; simplify_eq/=. *) *)


  (* Wait, this is a syntactic type! *)
  Definition Pred := λI t, WP (t @: "isPred") {{v, ⟦
    (∀: tparam "A", (∀: p0 @; "A", (∀: p1 @; "A", TSing p0)))%ty ⟧ ids v}}.

  Lemma foo Γ (g : stys) : False.
    Import typing_stamped.
    move: (noneTypStronger Γ) => /(stamp_objIdent_typed g).
    destruct 1 as (none' & g' & HeT%typing_obj_ident_to_typing & ? & ?); ev.
    edestruct foo1 as [σ [s Heq]] => //.
    (* intros (none' & g' & ?); ev.
    destruct (stamp_typed (noneTyp Γ)) as (e' & g'' & HeT & ?). *)

    have ?: Pred none'.
    rewrite ->Heq in *; cbn in *.
    rewrite (lock none') in Heq.
    simplify_eq/=.
    unfold from_option in *; case_match; simplify_eq/=.
    (* destruct none' as [v'| | | ]; simplify_eq/=.
    destruct v' as [| | | ]; simplify_eq/=. *)
    have HeTs: Γ ⊨[ Vs⟦ g' ⟧ ] none' : hclose hnoneSingT. {
      apply fundamental_typed. rewrite -lock in Heq. rewrite Heq. apply HeT.
    }
    rewrite /Pred.
    Require Import D.pure_program_logic.weakestpre.
    rewrite -lock in Heq; subst.
    iApply (wp_bind (ectx_language.fill [ProjCtx _])).
    iApply wp_wand.
    iDestruct (HeTs with "[]") as "#H".
    iSpecialize ("H" $! ids with
    admit.
    iApply "H".
    rewrite -wp_value' /=.
    cbn.

    smart_wp_bind (ProjCtx "isPred") v "#Hv {HE}" ("HE" with "[]").
    iApply wp_bind.
    iApply wp_pure_step_later.
    cbn.
    have := fundamental_typed => /(_ dlangΣ HeT).
    move => [e' [g ?].

