(** * Logical relation and semantic judgments. *)
From D Require Export iris_prelude proper lty lr_syn_aux.
From D Require Import iris_extra.det_reduction.
From D Require Import swap_later_impl.
From D.Dot Require Import syn path_repl.
From D.Dot Require Export dlang_inst path_wp.
From D.pure_program_logic Require Import weakestpre.
From D.Dot Require Export dot_lty dot_semtypes sem_kind_dot.

Unset Program Cases.
Set Suggest Proof Using.
Set Default Proof Using "Type*".

Implicit Types (Σ : gFunctors)
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : env) (l : label) (T : ty) (K : kind) (Γ : ctx).

(** [CTyInterp] is an (operational) typeclass, implemented by the gDOT
logical relation. *)
Class CTyInterp Σ :=
  clty_interp : ty → clty Σ.
#[global] Arguments clty_interp {_ _} !_ /.
Notation "C⟦ T ⟧" := (clty_interp T).

Class SfKindInterp Σ :=
  sf_kind_interp : kind → sf_kind Σ.
#[global] Arguments sf_kind_interp {_ _} !_ /.
Notation "K⟦ K ⟧" := (sf_kind_interp K).

(** *** Define various notations on top of [clty_interp]. *)
(** Definition interpretation of types (Fig. 9). *)
Notation "Ds⟦ T ⟧" := (clty_dslty C⟦ T ⟧).

(* We could inline [pty_interp] inside the [V⟦ _ ⟧] notation, but I suspect
the [V⟦ _ ⟧*] notation needs [pty_interp] to be a first-class function. *)
Definition pty_interp `{CTyInterp Σ} T : oltyO Σ := clty_olty C⟦ T ⟧.
(* #[global] Arguments pty_interp {_ _} !_ /. *)
#[global] Arguments pty_interp : simpl never.

(** * Value interpretation of types (Fig. 9). *)
Notation "V⟦ T ⟧" := (pty_interp T).
Notation "V⟦ Γ ⟧*" := (fmap (M := list) pty_interp Γ).
Notation "E⟦ T ⟧" := (sE⟦ V⟦ T ⟧ ⟧).

(** ** Binding lemmas about gDOT logical relations. *)
Class CTyInterpLemmas Σ `{!CTyInterp Σ} := {
  interp_subst_compose_ind T {args} ρ1 ρ2 v:
    V⟦ T.|[ρ1] ⟧ args ρ2 v ⊣⊢ V⟦ T ⟧ args (ρ1 >> ρ2) v;
}.

(** Corollaries of [CTyInterpLemmas]. *)
Section logrel_binding_lemmas.
  Context `{Htil : CTyInterpLemmas Σ}.
  Set Default Proof Using "Type*".

  Lemma interp_subst_compose T {args} ρ1 ρ2 ρ3:
    ρ1 >> ρ2 = ρ3 → V⟦ T.|[ρ1] ⟧ args ρ2 ≡ V⟦ T ⟧ args ρ3.
  Proof. move=> <- v. exact: interp_subst_compose_ind. Qed.

  Lemma interp_weaken_one τ ρ {args} :
    V⟦ shift τ ⟧ args ρ ≡ V⟦ τ ⟧ args (stail ρ).
  Proof. apply interp_subst_compose. autosubst. Qed.

  Lemma interp_subst_one T v w ρ {args} :
    V⟦ T.|[v/] ⟧ args ρ ≡ V⟦ T ⟧ args (v.[ρ] .: ρ).
  Proof. apply interp_subst_compose. autosubst. Qed.

  Lemma interp_subst_ids T ρ {args} : V⟦ T ⟧ args ρ ≡ V⟦ T.|[ρ] ⟧ args ids.
  Proof. symmetry. apply interp_subst_compose. autosubst. Qed.

  (**
    We have, unconditionally, that
    V⟦ T.|[∞ σ] ⟧ args ρ = V⟦ T ⟧ args (∞ σ >> ρ).

    But [∞ σ >> ρ] and [∞ σ.|[ρ]] are only equal for
    [length σ] entries.
  *)
  Lemma interp_commute_finsubst_cl T σ ρ v (HclT : nclosed T (length σ)) args :
    V⟦ T.|[∞ σ] ⟧ args ρ v ≡ V⟦ T ⟧ args (∞ σ.|[ρ]) v.
  Proof.
    rewrite interp_subst_compose_ind !(interp_subst_ids T) -hsubst_comp.
    (* *The* step requiring [HclT]. *)
    by rewrite (subst_compose HclT).
  Qed.

  (** Substitution on semantic types commutes with the semantics. *)
  Lemma interp_commute_subst T σ : V⟦ T.|[σ] ⟧ ≡ V⟦ T ⟧.|[σ].
  Proof. intros ???; apply interp_subst_compose_ind. Qed.

  Lemma interp_commute_weaken T n : V⟦ shiftN n T ⟧ ≡ shiftN n V⟦ T ⟧.
  Proof. apply (interp_commute_subst _ (ren (+n))). Qed.

  Lemma interp_commute_weaken_one T : V⟦ shift T ⟧ ≡ shift V⟦ T ⟧.
  Proof. apply interp_commute_weaken. Qed.

  Lemma interp_commute_subst_one T v : V⟦ T.|[ v /] ⟧ ≡ V⟦ T ⟧.|[ v /].
  Proof. apply (interp_commute_subst _ (v .: ids)). Qed.
End logrel_binding_lemmas.


Section log_rel.
  Context `{HdotG: !dlangG Σ}.
(** The logical relation on values is [V⟦T⟧]. We also define the logical
    relation on definitions [Ds⟦T⟧].

    Both definitions follow the one on paper; concretely, they are defined
    through [C⟦T⟧] in instance [dot_ty_interp].

    Binding and closing substitutions:

    Both relations interprets *open* types into predicates over values that
    are meant to be closed. So for instance [V⟦T⟧ T args ρ v] applies substitution [ρ]
    to [T], but not to [v]. We don't actually require that [v] be closed.

    Semantic judgements must apply instead to open subjects (terms/value/paths),
    so they apply substitutions to their subject.

    Additionally, both apply to *stamped* syntax, hence they only expect
    [dtysem] and not [dtysyn] for type member definitions.
 *)

  (** Dispatch function defining [V⟦ T ⟧] and [Ds⟦ T ⟧]. *)
  (* Observe the naming pattern for semantic type constructors:
  replace T by o (for most constructors) or by c (for constructors producing
  cltys). *)
  Implicit Type (hrec : ty -d> hoEnvD Σ).
  Implicit Type (clrec : ty -d> cltyO Σ).

  Fixpoint kind_rec clrec (K : kind) {struct K} : sf_kind Σ :=
    let rec_ty := ty_rec clrec : CTyInterp Σ in
    let rec_kind := kind_rec clrec : SfKindInterp Σ in
    match K with
    | kintv L U => sf_kintv V⟦ L ⟧ V⟦ U ⟧
    | kpi S K => sf_kpi V⟦ S ⟧ K⟦ K ⟧
    end
   with ty_rec clrec (T : ty) {struct T} : clty Σ :=
    let rec_ty := ty_rec clrec : CTyInterp Σ in
    let rec_kind := kind_rec clrec : SfKindInterp Σ in
    let hrec T := clty_olty $ clrec T in
    match T with
    | kTTMem l K => cTMemK l hrec K⟦ K ⟧
    | TVMem l T' => cVMem l V⟦ T' ⟧
    | TAnd T1 T2 => cAnd C⟦ T1 ⟧ C⟦ T2 ⟧
    | TTop => cTop

    (* The remaining types are not useful for definition typing. *)
    | TBot => olty2clty oBot
    | TOr T1 T2 => olty2clty $ oOr V⟦ T1 ⟧ V⟦ T2 ⟧
    | TLater T => olty2clty $ oLater V⟦ T ⟧
    | TPrim b => olty2clty $ oPrim b
    | TAll T1 T2 => olty2clty $ oAll V⟦ T1 ⟧ V⟦ T2 ⟧
    | TMu T => olty2clty $ oMu V⟦ T ⟧
    | kTSel n p l => olty2clty $ oSel p l hrec
    | TSing p => olty2clty $ oSing p
    | TLam T => olty2clty $ oLam V⟦ T ⟧
    | TApp T p => olty2clty $ oTApp V⟦ T ⟧ p
    end.

  (* Notation Contractive2 f := (∀ n, Proper (dist_later n ==> dist_later n ==> dist n) f). *)
  Section interp_contractive.
    Context (ri1 ri2 : ty -d> cltyO Σ).

    Lemma interp_contractive_mut n (Hri : dist_later n ri1 ri2) :
      (∀ T, ty_rec ri1 T ≡{n}≡ ty_rec ri2 T) ∧
      (∀ K, kind_rec ri1 K ≡{n}≡ kind_rec ri2 K).
    Proof.
      apply tp_kn_mut_ind; simpl; [done|done|..]; intros *.
      all: rewrite /pty_interp/clty_interp/sf_kind_interp.
      Time all: intros; try by repeat (hof_eq_app || f_equiv).
      all: repeat (hof_eq_app || f_contractive || f_equiv).
      all: intros ????; apply clty_olty_ne, Hri.
    Qed.
  End interp_contractive.

  #[global] Instance kind_rec_contractive :
    Contractive (kind_rec : _ -d> kind -d> sf_kindO Σ).
  Proof. by move=> /= n ri1 ri2 Hri x; apply interp_contractive_mut. Qed.
  #[global] Instance ty_rec_contractive :
    Contractive (ty_rec : _ -d> ty -d> cltyO Σ).
  Proof. by move=> /= n ri1 ri2 Hri x; apply interp_contractive_mut. Qed.

  #[global] Instance ty_interp : CTyInterp Σ := fixpoint ty_rec.
  #[global] Arguments clty_interp {_ _} _ : simpl never.
  #[global] Instance dot_kind_interp : SfKindInterp Σ := kind_rec ty_interp.
  #[global] Arguments sf_kind_interp {_ _} _ : simpl never.

  Lemma fixpoint_interp_eq1 T : C⟦ T ⟧ ≡ ty_rec ty_interp T.
  Proof. apply: fixpoint_unfold. Qed.
  Ltac rewrite_interp := repeat (rewrite fixpoint_interp_eq1 //=; repeat f_equiv).
  Lemma fixpoint_interp_eq : ty_interp ≡@{ty -d> _} ty_rec ty_interp.
  Proof. apply: fixpoint_unfold. Qed.
  #[global] Instance kind_rec_ne :
    NonExpansive (kind_rec : _ -d> kind -d> sf_kindO Σ) := _.
  #[global] Instance kind_rec_proper :
    Proper1 (kind_rec : _ -d> kind -d> sf_kindO Σ) := _.

  Lemma krec_unfold0 : kind_rec (ty_rec ty_interp) ≡@{kind -d> sf_kindO Σ} kind_rec ty_interp.
  Proof. by rewrite /sf_kind_interp/dot_kind_interp -fixpoint_unfold. Qed.
  Lemma krec_unfold K : K⟦ K ⟧ ≡ kind_rec ty_interp K.
  Proof. done. Qed.
  Lemma trec_fold0 : ty_rec ty_interp ≡@{ty -d> cltyO Σ} ty_interp.
  Proof. apply symmetry, fixpoint_unfold. Qed.

  Lemma kinterp_kintv L U : K⟦ kintv L U ⟧ ≡ sf_kintv V⟦ L ⟧ V⟦ U ⟧.
  Proof. apply sf_kintv_proper; apply trec_fold0. Qed.
  Lemma kinterp_kpi S K : K⟦ kpi S K ⟧ ≡ sf_kpi V⟦ S ⟧ K⟦ K ⟧.
  Proof. apply sf_kpi_proper. apply trec_fold0. done. Qed.
  Definition klr := (kinterp_kintv, kinterp_kpi).
  Ltac kgo := rewrite ?klr.

    (* | kintv L U => sf_kintv V⟦ L ⟧ V⟦ U ⟧
    | kpi S K => sf_kpi V⟦ S ⟧ K⟦ K ⟧ *)

  Notation cBot := (olty2clty oBot).
  Notation cOr T1 T2 := (olty2clty $ oOr T1 T2).
  Notation cLater T := (olty2clty $ oLater T).
  Notation cPrim b := (olty2clty $ oPrim b).
  Notation cAll T1 T2 := (olty2clty $ oAll T1 T2).
  Notation cMu T := (olty2clty $ oMu T).
  Notation cSel p l pty := (olty2clty $ oSel p l pty).
  Notation cSing p := (olty2clty $ oSing p).
  Notation cLam T := (olty2clty $ oLam T).
  Notation cApp T p := (olty2clty $ oTApp T p).

  (* #[global] Arguments sf_kind_interp {_ _} _ : simpl never. *)
  Lemma cinterp_TTop : C⟦ TTop ⟧ ≡ cTop.
  Proof. apply fixpoint_interp_eq1. Qed.
  Lemma cinterp_TBot : C⟦ TBot ⟧ ≡ cBot.
  Proof. apply fixpoint_interp_eq1. Qed.

  Ltac go :=
    rewrite fixpoint_interp_eq1 /= /pty_interp/clty_interp//=;
    by rewrite -fixpoint_unfold.
  Lemma cinterp_kTTMem l K1 : C⟦ kTTMem l K1 ⟧ ≡ cTMemK l pty_interp K⟦ K1 ⟧.
  Proof. go. Qed.
  Lemma cinterp_kTSel n p l : C⟦ kTSel n p l ⟧ ≡ cSel p l pty_interp.
  Proof. go. Qed.

  Lemma cinterp_TAnd T1 T2 : C⟦ TAnd T1 T2 ⟧ ≡ cAnd C⟦ T1 ⟧ C⟦ T2 ⟧.
  Proof. by rewrite !fixpoint_interp_eq1. Qed.
  (* Lemma cinterp_TAnd T1 T2 args : C⟦ TAnd T1 T2 ⟧ args ≡ cAnd C⟦ T1 ⟧ C⟦ T2 ⟧ args .
  Proof. rewrite fixpoint_interp_eq1/=. Qed. *)
  Lemma cinterp_TOr T1 T2 : C⟦ TOr T1 T2 ⟧ ≡ cOr V⟦ T1 ⟧ V⟦ T2 ⟧.
  Proof. go. Qed.
  Lemma cinterp_TLater T1 : C⟦ TLater T1 ⟧ ≡ cLater V⟦ T1 ⟧.
  Proof. go. Qed.
  Lemma cinterp_TAll T1 T2 : C⟦ TAll T1 T2 ⟧ ≡ cAll V⟦ T1 ⟧ V⟦ T2 ⟧.
  Proof. go. Qed.
  Lemma cinterp_TMu T1 : C⟦ TMu T1 ⟧ ≡ cMu V⟦ T1 ⟧.
  Proof. go. Qed.
  Lemma cinterp_TVMem l T1 : C⟦ TVMem l T1 ⟧ ≡ cVMem l V⟦ T1 ⟧.
  Proof. go. Qed.
  Lemma cinterp_TPrim b : C⟦ TPrim b ⟧ ≡ cPrim b.
  Proof. apply fixpoint_interp_eq1. Qed.
  Lemma cinterp_TSing p : C⟦ TSing p ⟧ ≡ cSing p.
  Proof. apply fixpoint_interp_eq1. Qed.
  Lemma cinterp_TLam T1 : C⟦ TLam T1 ⟧ ≡ cLam V⟦ T1 ⟧.
  Proof. go. Qed.
  Lemma cinterp_TApp T1 p : C⟦ TApp T1 p ⟧ ≡ cApp V⟦ T1 ⟧ p.
  Proof. go. Qed.
  Definition clr :=
    (cinterp_TTop, cinterp_TBot, cinterp_TAnd,
    cinterp_TOr, cinterp_TLater, cinterp_TAll, cinterp_TMu, cinterp_TVMem,
    cinterp_kTTMem, cinterp_kTSel, cinterp_TPrim, cinterp_TSing, cinterp_TLam, cinterp_TApp).

  Ltac go ::= rewrite /pty_interp clr //.

  Lemma interp_TTop : V⟦ TTop ⟧ ≡ oTop.
  Proof. go. Qed.
  Lemma interp_TBot : V⟦ TBot ⟧ ≡ oBot.
  Proof. go. Qed.
  Lemma interp_TAnd T1 T2 : V⟦ TAnd T1 T2 ⟧ ≡ oAnd V⟦ T1 ⟧ V⟦ T2 ⟧.
  Proof. go. Qed.
  Lemma interp_TOr T1 T2 : V⟦ TOr T1 T2 ⟧ ≡ oOr V⟦ T1 ⟧ V⟦ T2 ⟧.
  Proof. go. Qed.
  Lemma interp_TLater T1 : V⟦ TLater T1 ⟧ ≡ oLater V⟦ T1 ⟧.
  Proof. go. Qed.
  Lemma interp_TAll T1 T2 : V⟦ TAll T1 T2 ⟧ ≡ oAll V⟦ T1 ⟧ V⟦ T2 ⟧.
  Proof. go. Qed.
  Lemma interp_TMu T1 : V⟦ TMu T1 ⟧ ≡ oMu V⟦ T1 ⟧.
  Proof. go. Qed.
  Lemma interp_TVMem l T1 : V⟦ TVMem l T1 ⟧ ≡ oVMem l V⟦ T1 ⟧.
  Proof. go. Qed.
  Lemma interp_kTTMem l K1 : V⟦ kTTMem l K1 ⟧ ≡ oTMemK l pty_interp K⟦ K1 ⟧.
  Proof. go. Qed.
  Lemma interp_kTSel n p l : V⟦ kTSel n p l ⟧ ≡ oSel p l pty_interp.
  Proof. go. Qed.
  Lemma interp_TPrim b : V⟦ TPrim b ⟧ ≡ oPrim b.
  Proof. go. Qed.
  Lemma interp_TSing p : V⟦ TSing p ⟧ ≡ oSing p.
  Proof. go. Qed.
  Lemma interp_TLam T1 : V⟦ TLam T1 ⟧ ≡ oLam V⟦ T1 ⟧.
  Proof. go. Qed.
  Lemma interp_TApp T1 p : V⟦ TApp T1 p ⟧ ≡ oTApp V⟦ T1 ⟧ p.
  Proof. go. Qed.
  (** Unfolding lemma for [TAnd]: defined because [simpl] on the LHS produces
      [oAnd C⟦ T1 ⟧ C⟦ T2 ⟧]. *)
  Lemma interp_TAnd_eq T1 T2 : V⟦ TAnd T1 T2 ⟧ ≡ oAnd V⟦ T1 ⟧ V⟦ T2 ⟧.
  Proof. apply interp_TAnd. Qed.

  Definition vlr :=
    (interp_TTop, interp_TBot, interp_TAnd,
    interp_TOr, interp_TLater, interp_TAll, interp_TMu, interp_TVMem,
    interp_kTTMem, interp_kTSel, interp_TPrim, interp_TSing, interp_TLam, interp_TApp).
  Ltac vgo := rewrite ?vlr.

  (** Binding lemmas for [V⟦ T ⟧] and [K⟦ T ⟧]. *)
  Lemma mut_interp_subst_compose_ind :
    (∀ T args ρ1 ρ2 v,
      V⟦ T.|[ρ1] ⟧ args ρ2 v ⊣⊢ V⟦ T ⟧ args (ρ1 >> ρ2) v) ∧
    (∀ K ρ1 ρ2 τ1 τ2,
      K⟦ K.|[ρ1] ⟧ ρ2 τ1 τ2 ⊣⊢ K⟦ K ⟧ (ρ1 >> ρ2) τ1 τ2).
  Proof.
    apply tp_kn_mut_ind; intros; vgo; kgo;
      rewrite /= /sr_kintv /subtype_lty; properness;
      rewrite ?scons_up_swap ?hsubst_comp; trivial.
    all: try by apply path_wp_proper => ?.
  Qed.
  (*
  Lemma vrec3 T args ρ v : V⟦ T ⟧ args ρ v ≡ ty_rec ty_interp T.
  Proof. apply: fixpoint_unfold. Qed.
    rewrite trec_fold0.
    eapply H.
    apply H.
    rewrite /pty_interp/clty_interp.
    f_equiv.
    Fail rewrite -fixpoint_interp_eq1.
    Fail rewrite fixpoint_unfold.
    Fail rewrite -fixpoint_unfold.
    all: unfold pty_interp in *.
    rewrite krec_unfold.
    f_equiv.
      rewrite ?scons_up_swap ?hsubst_comp; trivial.
    apply clty_o
      rewrite -fixpoint_interp_eq1. ixpoint_unfold.
    all: vgo.



    apply tp_kn_mut_ind; intros.
    all: vgo.

    all: rewrite /= /sr_kintv /subtype_lty;
      properness;
      rewrite ?scons_up_swap ?hsubst_comp; trivial.
    all: try by apply path_wp_proper => ?.
    rewrite /pty_interp.
    f_equiv.
      rewrite ?scons_up_swap ?hsubst_comp; trivial.
    apply clty_o
      rewrite -fixpoint_interp_eq1. ixpoint_unfold.
    all: vgo.


    rewrite /sr_kintv /subtype_lty. vgo; simpl.

    apply H.
    trivial.
    rewrite /pty_interp; apply tp_kn_mut_ind; intros.
    simpl.

      rewrite /= /pty_interp.
      eapply clty_olty_proper.
      rewrite ?clr. /sr_kintv /subtype_lty; properness;
      rewrite ?scons_up_swap ?hsubst_comp; trivial.
    all: by apply path_wp_proper => ?.
  Qed. *)

  #[global] Instance pinterp_lemmas: CTyInterpLemmas Σ.
  Proof. split. apply mut_interp_subst_compose_ind. Qed.

  Lemma kind_interp_subst_compose_ind K ρ1 ρ2 τ1 τ2 :
      K⟦ K.|[ρ1] ⟧ ρ2 τ1 τ2 ⊣⊢ K⟦ K ⟧ (ρ1 >> ρ2) τ1 τ2.
  Proof. apply mut_interp_subst_compose_ind. Qed.

  Definition idtp  Γ T l d     := sdtp l d  V⟦Γ⟧* C⟦T⟧.
  Definition idstp Γ T ds      := sdstp ds  V⟦Γ⟧* C⟦T⟧.
  Definition ietp  Γ T e       := setp e    V⟦Γ⟧* V⟦T⟧.
  Definition istpd i Γ T1 T2   := sstpd i   V⟦Γ⟧* V⟦T1⟧ V⟦T2⟧.
  Definition iptp  Γ T p i     := sptp p i  V⟦Γ⟧* V⟦T⟧.
End log_rel.

Notation "G⟦ Γ ⟧ ρ" := (sG⟦ V⟦ Γ ⟧* ⟧* ρ) (at level 10).

(** Single-definition typing *)
Notation "Γ ⊨ {  l := d  } : T" := (idtp Γ T l d) (at level 74, d, l, T at next level).
(** Multi-definition typing *)
Notation "Γ ⊨ds ds : T" := (idstp Γ T ds) (at level 74, ds, T at next level).
(** Expression typing *)
Notation "Γ ⊨ e : T" := (ietp Γ T e) (at level 74, e, T at next level).
Notation "Γ ⊨p p : T , i" := (iptp Γ T p i) (at level 74, p, T, i at next level).
Notation "Γ ⊨ T1 <:[ i  ] T2" := (istpd i Γ T1 T2) (at level 74, T1, T2 at next level).

(** ** Show these typing judgments are equivalent to what we present in the paper. *)
Section judgment_definitions.
  Context `{HdotG: !dlangG Σ}.

  Lemma idstp_eq Γ T ds : Γ ⊨ds ds : T ⊣⊢
    |==> ⌜wf_ds ds⌝ ∧ ∀ ρ, ⌜path_includes (pv (ids 0)) ρ ds ⌝ → G⟦Γ⟧ ρ → Ds⟦T⟧ ρ ds.|[ρ].
  Proof. reflexivity. Qed.

  Lemma ietp_eq Γ e T :
    Γ ⊨ e : T ⊣⊢ |==> ∀ ρ, G⟦Γ⟧ ρ → E⟦T⟧ ρ (e.|[ρ]).
  Proof. reflexivity. Qed.

  Lemma istpd_eq Γ T1 i T2 :
    Γ ⊨ T1 <:[i] T2 ⊣⊢
    |==> ∀ ρ v, G⟦Γ⟧ ρ → ▷^i (V⟦T1⟧ anil ρ v → V⟦T2⟧ anil ρ v).
  Proof. apply sstpd_eq. Qed.

  Lemma iptp_eq Γ p T i :
    Γ ⊨p p : T , i ⊣⊢
    |==> ∀ ρ, G⟦Γ⟧ ρ →
      ▷^i path_wp (p.|[ρ]) (λ v, V⟦T⟧ anil ρ v).
  Proof. reflexivity. Qed.
End judgment_definitions.

Section misc_lemmas.
  Context `{HdotG: !dlangG Σ}.

  Lemma iterate_TLater_oLater i (T : ty) :
    V⟦iterate TLater i T⟧ ≡ oLaterN i V⟦T⟧.
  Proof. elim: i => [//|i IHi] ???. by rewrite !iterate_S vlr /= IHi. Qed.

End misc_lemmas.

Section path_repl_lemmas.
  Context `{!dlangG Σ}.
  Implicit Types (φ : vl -d> iPropO Σ).

  Let fundamental_ty_path_repl_def p q T1 T2 := V⟦ T1 ⟧ ~sTpP[ p := q ]* V⟦ T2 ⟧.
  Let fundamental_kn_path_repl_def p q K1 K2 := K⟦ K1 ⟧ ~sKpP[ p := q ]* K⟦ K2 ⟧.

  Local Lemma fundamental_ty_kn_mut_path_repl p q :
    (∀ T1 T2 (Hrew : T1 ~Tp[ p := q ] T2), fundamental_ty_path_repl_def p q T1 T2) ∧
    (∀ K1 K2 (Hrew : K1 ~Kp[ p := q ] K2), fundamental_kn_path_repl_def p q K1 K2).
  Proof.
    apply ty_kind_path_repl_mut_ind;
    rewrite /fundamental_ty_path_repl_def /fundamental_kn_path_repl_def
      /sem_ty_path_repl /sem_kind_path_repl; intros.
      all: rewrite ?vlr ?klr /=.
      all: rewrite /sr_kintv /subtype_lty/=; intros;
      try match goal with
      | H : context [equiv _ _] |- _ => rename H into IHHrew
      end;
      properness.
    all: eauto 2.
    all: by [ apply: path_replacement_equiv
            | apply: rewrite_path_path_repl
            | apply IHHrew; rewrite ?hsubst_comp
            | apply: path_wp_proper => ?; exact: IHHrew ].
  Qed.
  Lemma fundamental_ty_path_repl {p q T1 T2}
    (Hrew : T1 ~Tp[ p := q ] T2) :
    V⟦ T1 ⟧ ~sTpP[ p := q ]* V⟦ T2 ⟧.
  Proof. by apply fundamental_ty_kn_mut_path_repl. Qed.
  Lemma fundamental_kn_path_repl {p q K1 K2}
    (Hrew : K1 ~Kp[ p := q ] K2) :
    K⟦ K1 ⟧ ~sKpP[ p := q ]* K⟦ K2 ⟧.
  Proof. by apply fundamental_ty_kn_mut_path_repl. Qed.

  Lemma fundamental_ty_path_repl_rtc {p q T1 T2}
    (Hrew : T1 ~Tp[ p := q ]* T2) :
    V⟦ T1 ⟧ ~sTpP[ p := q ]* V⟦ T2 ⟧.
  Proof.
    move=> args ρ v Hal. elim: Hrew => [//|T {}T1 {}T2 Hr _ <-].
    apply (fundamental_ty_path_repl Hr), Hal.
  Qed.

  Lemma rewrite_ty_path_repl_rtc {p q T1 T2 args ρ}
    (Hrepl : T1 ~Tp[ p := q ]* T2)
    (Hal : alias_paths p.|[ρ] q.|[ρ]): (* p : q.type *)
    V⟦ T1 ⟧ args ρ ≡ V⟦ T2 ⟧ args ρ.
  Proof. intros v. apply: (fundamental_ty_path_repl_rtc Hrepl) Hal. Qed.

  (**
  Prove that semantic and syntactic substitution of paths in types agree.
  However, this proof only works for paths that normalize; that's because
  [V⟦ T ⟧ .sTp[ p /] args ρ v] asserts that [p] terminates, while
  [V⟦ T' ⟧ args ρ v] need not assert that (say, because [T'] is
  [TOr TTop (TSel p l)].
  *)
  Lemma sem_psubst_one_eq {T T' args p v ρ}
    (Hrepl : T .Tp[ p /]~ T')
    (Hal : alias_paths p.|[ρ] (pv v)) :
    V⟦ T' ⟧ args ρ ≡ V⟦ T ⟧ .sTp[ p /] args ρ.
  Proof.
    rewrite -(interp_weaken_one T' (v .: ρ)) => w.
    rewrite -(rewrite_ty_path_repl_rtc Hrepl) /=.
    by rewrite (alias_paths_elim_eq _ Hal) path_wp_pv_eq.
    by rewrite hsubst_comp ren_scons /= alias_paths_symm.
  Qed.

  Lemma psubst_one_repl {T T' args p v w ρ}
    (Hr : T .Tp[ p /]~ T') (Hal : alias_paths p.|[ρ] (pv v)) :
    V⟦ T ⟧ args (v .: ρ) w ≡ V⟦ T' ⟧ args ρ w.
  Proof. by rewrite (sem_psubst_one_eq Hr Hal) (sem_psubst_one_repl Hal). Qed.
End path_repl_lemmas.

(** Backward compatibility. *)
Notation "⟦ T ⟧" := (oClose V⟦ T ⟧).

Definition lr := (@fmap_cons, @iterate_TLater_oLater, @vlr, @klr, @clr).
Ltac rw := rewrite /ietp /idstp /idtp /iptp /istpd ?lr.

Import dlang_adequacy.

(** Adequacy of normalization for gDOT paths. *)
Lemma ipwp_gs_adequacy Σ `{HdlangG : !dlangG Σ} `{!SwapPropI Σ} {p T i}
  (Hwp : ∀ `(Hdlang : !dlangG Σ) `(!SwapPropI Σ), ⊢ [] ⊨p p : T , i):
  terminates (path2tm p).
Proof.
  eapply (@soundness (iResUR Σ) _ i).
  apply (bupd_plain_soundness _).
  iApply ipwp_terminates.
  iApply Hwp.
Qed.
