(** * Semantic domains for DOT logical relations. *)
From iris.proofmode Require Import tactics.
From D Require Export iris_prelude proper lty lr_syn_aux.
From D.Dot Require Import syn.
From D.Dot Require Export dlang_inst.

Unset Program Cases.
Set Suggest Proof Using.
Set Default Proof Using "Type".

Implicit Types (Σ : gFunctors)
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : var → vl) (l : label).

Include Lty VlSorts dlang_inst.

(** The semantics of a DOT type as a single-definition type is a a persistent
predicate over the definition, indexed by an environment. *)
Notation dlty Σ := (env → iPPred dm Σ).
Notation dltyO Σ := (env -d> iPPredO dm Σ).
Notation Dlty T := (λ ρ, IPPred (λI d, T ρ d)).

Notation dslty Σ := (env → iPPred dms Σ).
Definition dsltyO Σ := env -d> iPPredO dms Σ.
Notation Dslty T := (λ ρ, IPPred (λI ds, T ρ ds)).

(** ** A "coherent" logical type, containing all semantics of a type.
That is, semantics for both definition lists and values, and proofs that they
agree appropriately. *)
Record clty {Σ} := _Clty {
  clty_dslty :> dslty Σ;
  clty_olty : oltyO Σ;
  clty_def2defs_head {l d ds ρ} :
    clty_dslty ρ [(l, d)] ⊢ clty_dslty ρ ((l, d) :: ds);
  clty_mono {l d ds ρ} :
    dms_hasnt ds l →
    clty_dslty ρ ds ⊢ clty_dslty ρ ((l, d) :: ds);
  clty_commute {ds ρ} :
    clty_dslty ρ (selfSubst ds) ⊢ clty_olty anil ρ (vobj ds);
}.
Add Printing Constructor clty.
Notation c2o := clty_olty.

Arguments clty : clear implicits.
Arguments _Clty {_}.
Notation Clty TD T := (_Clty TD T _ _ _).
Arguments clty_dslty {_} !_.
Instance: Params (@clty_dslty) 1 := {}.
Arguments clty_olty {_} !_.
Instance: Params (@clty_olty) 1 := {}.

Section clty_ofe.
  Context {Σ}.

  Let iso := (λ T : clty Σ, (clty_dslty T : _ -d> _, clty_olty T)).
  Instance clty_equiv : Equiv (clty Σ) := λ A B, iso A ≡ iso B.
  Instance clty_dist : Dist (clty Σ) := λ n A B, iso A ≡{n}≡ iso B.
  Lemma clty_ofe_mixin : OfeMixin (clty Σ).
  Proof. exact: (iso_ofe_mixin iso). Qed.
End clty_ofe.
Canonical Structure cltyO Σ := OfeT (clty Σ) clty_ofe_mixin.

Section clty_ofe_proper.
  Context {Σ}.

  #[global] Instance clty_olty_ne : NonExpansive (clty_olty (Σ := Σ)).
  Proof. by move=> ???[/= _ H]. Qed.
  #[global] Instance clty_olty_proper :
    Proper ((≡) ==> (≡)) (clty_olty (Σ := Σ)) := ne_proper _.

  #[global] Instance clty_dslty_ne n :
    Proper (dist n ==> (=) ==> dist n) (clty_dslty (Σ := Σ)).
  Proof. by move=> ??[/= H _] ??->. Qed.
  #[global] Instance clty_dslty_proper :
    Proper ((≡) ==> (=) ==> (≡)) (clty_dslty (Σ := Σ)).
  Proof. by move=> ??[/= H _] ??->. Qed.
End clty_ofe_proper.

(** *** Helpers for constructing [clty]. *)
Definition lift_dty_dms `{!dlangG Σ} l (TD : dltyO Σ) : dsltyO Σ := Dslty (λI ρ ds,
  ∃ d, ⌜ dms_lookup l ds = Some d ⌝ ∧ TD ρ d).
Instance: Params (@lift_dty_dms) 3 := {}.

Definition lift_dty_vl `{!dlangG Σ} l (TD : dltyO Σ) : oltyO Σ :=
  olty0 (λI ρ v, ∃ d, ⌜v @ l ↘ d ⌝ ∧ TD ρ d).
Instance: Params (@lift_dty_vl) 3 := {}.

(** This definition is only useful to show in [lift_dty_vl_equiv_paper] that
certain definitions we give are equivalent to the ones in the paper. *)
Definition lift_dty_vl_paper `{!dlangG Σ} (TD : dsltyO Σ) : oltyO Σ := olty0 (λI ρ v,
  ∃ ds, ⌜v = vobj ds⌝ ∧ TD ρ (selfSubst ds)).

Section lift_dty_lemmas.
  Context `{HdotG: !dlangG Σ}.

  Lemma lift_dty_vl_equiv_paper l T :
    lift_dty_vl l T ≡ lift_dty_vl_paper (lift_dty_dms l T).
  Proof.
    (* The proof is just a quantifier swap. *)
    move=> args ρ v /=. rewrite bi_exist_nested_swap; f_equiv => d.
    setoid_rewrite (assoc bi_and); rewrite -and_exist_r /objLookup; f_equiv.
    by iIntros "!% /=".
  Qed.

  #[global] Instance lift_dty_dms_ne l : NonExpansive (lift_dty_dms l).
  Proof. rewrite /lift_dty_dms/= => ??? ??/=; properness; solve_proper_ho. Qed.
  #[global] Instance lift_dty_dms_proper l :
    Proper ((≡) ==> (≡)) (lift_dty_dms l) := ne_proper _.

  #[global] Instance lift_dty_vl_ne l : NonExpansive (lift_dty_vl l).
  Proof. rewrite /lift_dty_vl => ??; simplify_eq; solve_proper_ho. Qed.
  #[global] Instance lift_dty_vl_proper l :
    Proper ((≡) ==> (≡)) (lift_dty_vl l) := ne_proper _.

  Lemma lift_dty_dms_singleton_eq' (TD : dlty Σ) l1 l2 ρ d :
    lift_dty_dms l1 TD ρ [(l2, d)] ⊣⊢ ⌜ l1 = l2 ⌝ ∧ TD ρ d.
  Proof.
    iSplit; simpl; first by case_decide; iDestruct 1 as (d' [= ->]) "$".
    iDestruct 1 as (->) "H"; rewrite decide_True //; naive_solver.
  Qed.
  Lemma lift_dty_dms_singleton_eq (TD : dlty Σ) l ρ d :
    lift_dty_dms l TD ρ [(l, d)] ⊣⊢ TD ρ d.
  Proof.
    by rewrite lift_dty_dms_singleton_eq' pure_True // (left_id True%I bi_and).
  Qed.
End lift_dty_lemmas.

Program Definition olty2clty `{!dlangG Σ} (U : oltyO Σ) : cltyO Σ :=
  Clty ⊥ U.
Solve All Obligations with by iIntros.
#[global] Instance: Params (@olty2clty) 2 := {}.

Program Definition dty2clty `{!dlangG Σ} l (T : dltyO Σ) : cltyO Σ :=
  Clty (lift_dty_dms l T) (lift_dty_vl l T).
Next Obligation.
  intros. rewrite lift_dty_dms_singleton_eq' /=.
  iIntros "[-> ?]"; rewrite decide_True //. naive_solver.
Qed.
Next Obligation.
  rewrite /dms_hasnt /=; intros; case_decide; last done.
  by iDestruct 1 as (d' ?) "_"; simplify_eq.
Qed.
Next Obligation.
  intros; iDestruct 1 as (d Hl) "H". iExists d; iSplit; naive_solver.
Qed.
#[global] Instance: Params (@dty2clty) 3 := {}.

Section DefsTypes.
  Context `{HdotG: !dlangG Σ}.

  #[global] Instance olty2clty_ne : NonExpansive olty2clty.
  Proof. split; rewrite /=; by repeat f_equiv. Qed.
  #[global] Instance olty2clty_proper :
    Proper ((≡) ==> (≡)) olty2clty := ne_proper _.

  #[global] Instance dty2clty_ne l : NonExpansive (dty2clty l).
  Proof. split; rewrite /dty2clty/=; by repeat f_equiv. Qed.
  #[global] Instance dty2clty_proper l :
    Proper ((≡) ==> (≡)) (dty2clty l) := ne_proper _.

  Lemma dty2clty_singleton l (TD : dlty Σ) ρ d :
    dty2clty l TD ρ [(l, d)] ≡ TD ρ d.
  Proof. by rewrite lift_dty_dms_singleton_eq. Qed.

  Definition olty_dlty2clty_eq l (TD : dlty Σ) ρ v :
    c2o (dty2clty l TD) anil ρ v ⊣⊢ lift_dty_vl l TD anil ρ v := reflexivity _.

  Program Definition cTop : clty Σ := Clty (Dslty (λI _ _, True)) oTop.
  Solve All Obligations with eauto.

  #[global] Instance : Bottom (clty Σ) := olty2clty ⊥.

  Program Definition cAnd (Tds1 Tds2 : clty Σ): clty Σ :=
    Clty (Dslty (λI ρ ds, Tds1 ρ ds ∧ Tds2 ρ ds)) (oAnd (c2o Tds1) (c2o Tds2)).
  Next Obligation. intros. by rewrite /= -!clty_def2defs_head. Qed.
  Next Obligation. intros. by rewrite /= -!clty_mono. Qed.
  Next Obligation. intros. by rewrite /= -!clty_commute. Qed.

  #[global] Instance cAnd_ne : NonExpansive2 cAnd.
  Proof. split; rewrite /=; repeat f_equiv; solve_proper_ho. Qed.
  #[global] Instance cAnd_proper:
    Proper ((≡) ==> (≡) ==> (≡)) cAnd := ne_proper_2 _.

  Lemma cAnd_olty2clty T1 T2 :
    cAnd (olty2clty T1) (olty2clty T2) ≡ olty2clty (oAnd T1 T2).
  Proof. split=>??//=. apply: left_absorb. Qed.

  Lemma cAnd_cTop T : cAnd T cTop ≡@{clty Σ} T.
  Proof.
    split; [intros ρ ds | intros args ρ v]; apply: (right_id _ bi_and).
  Qed.
End DefsTypes.

#[global] Instance: Params (@cAnd) 1 := {}.

Implicit Types (T: ty).

(** [CTyInterp] is an (operational) typeclass, implemented by the gDOT
logical relation. *)
Class CTyInterp Σ :=
  clty_interp : ty → clty Σ.
#[global] Arguments clty_interp {_ _} !_ /.
Notation "C⟦ T ⟧" := (clty_interp T).

(** *** Define various notations on top of [clty_interp]. *)
(** Definition interpretation of types (Fig. 9). *)
Notation "Ds⟦ T ⟧" := (clty_dslty C⟦ T ⟧).

(* We could inline [pty_interp] inside the [V⟦ _ ⟧] notation, but I suspect
the [V⟦ _ ⟧*] notation needs [pty_interp] to be a first-class function. *)
Definition pty_interp `{CTyInterp Σ} T : oltyO Σ := clty_olty C⟦ T ⟧.
#[global] Arguments pty_interp {_ _} !_ /.

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
  Lemma interp_finsubst_commute_cl T σ ρ v (HclT : nclosed T (length σ)) args :
    V⟦ T.|[∞ σ] ⟧ args ρ v ≡ V⟦ T ⟧ args (∞ σ.|[ρ]) v.
  Proof.
    rewrite interp_subst_compose_ind !(interp_subst_ids T) -hsubst_comp.
    (* *The* step requiring [HclT]. *)
    by rewrite (subst_compose HclT).
  Qed.

  (** Substitution on semantic types commutes with the semantics. *)
  Lemma interp_subst_commute (T : ty) σ : V⟦ T.|[σ] ⟧ ≡ V⟦ T ⟧.|[σ].
  Proof. intros ???; apply interp_subst_compose_ind. Qed.
End logrel_binding_lemmas.
