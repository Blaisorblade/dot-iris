From iris.proofmode Require Import tactics.
From D Require Export iris_prelude proper lty lr_syn_aux.
From D.Dot Require Import syn.
From D.Dot Require Export dlang_inst.

(** * Semantic domains for DOT logical relations. *)

Unset Program Cases.
Set Suggest Proof Using.
Set Default Proof Using "Type".

Implicit Types (Σ : gFunctors)
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (vs : vls) (ρ : var → vl) (l : label).

Include Lty VlSorts dlang_inst.

(** The semantics of a DOT type as a single-definition type is a a persistent
predicate over the definition, indexed by an environment. *)
Notation dlty Σ := (env → iPPred dm Σ).
Notation dltyO Σ := (env -d> iPPredO dm Σ).
Notation Dlty T := (λ ρ, IPPred (λI d, T ρ d)).

Notation dslty Σ := (env → iPPred dms Σ).
Definition dsltyO Σ := env -d> iPPredO dms Σ.
Notation Dslty T := (λ ρ, IPPred (λI ds, T ρ ds)).

(** A "complete" logical type, containing all semantics of a type — for
definition lists, single definitions, and values; together with proofs that
they agree appropriately. *)
Record clty {Σ} := _Clty {
  clty_dslty :> dslty Σ;
  clty_olty :> oltyO Σ 0;
  clty_def2defs_head {l d ds ρ} :
    clty_dslty ρ [(l, d)] ⊢ clty_dslty ρ ((l, d) :: ds);
  clty_mono {l d ds ρ} :
    dms_hasnt ds l →
    clty_dslty ρ ds ⊢ clty_dslty ρ ((l, d) :: ds);
  clty_commute {ds ρ} :
    clty_dslty ρ (selfSubst ds) ⊢ clty_olty vnil ρ (vobj ds);
}.
Add Printing Constructor clty.

Arguments clty : clear implicits.
Arguments _Clty {_}.
Notation Clty TD T := (_Clty TD T _ _ _).
Arguments clty_dslty {_} !_ /.
Arguments clty_olty {_} !_ /.

Section clty_ofe.
  Context {Σ}.

  Let iso := (λ T : clty Σ, (clty_dslty T : _ -d> _, clty_olty T)).
  Instance clty_equiv : Equiv (clty Σ) := λ A B, iso A ≡ iso B.
  Instance clty_dist : Dist (clty Σ) := λ n A B, iso A ≡{n}≡ iso B.
  Lemma clty_ofe_mixin : OfeMixin (clty Σ).
  Proof. exact: (iso_ofe_mixin iso). Qed.
End clty_ofe.
Canonical Structure cltyO Σ := OfeT (clty Σ) clty_ofe_mixin.

Section DefsTypes.
  Context `{HdotG: !dlangG Σ}.

  Definition lift_dty_dms `{!dlangG Σ} l (TD : dltyO Σ) : dsltyO Σ := Dslty (λI ρ ds,
    ∃ d, ⌜ dms_lookup l ds = Some d ⌝ ∧ TD ρ d).
  Global Instance Proper_lift_dty_dms l : Proper ((≡) ==> (≡)) (lift_dty_dms l).
  Proof. rewrite /lift_dty_dms/= => ??? ??/=; properness; solve_proper_ho. Qed.

  Lemma lift_dty_dms_singleton_eq' (TD : dltyO Σ) l1 l2 ρ d :
    lift_dty_dms l1 TD ρ [(l2, d)] ⊣⊢ ⌜ l1 = l2 ⌝ ∧ TD ρ d.
  Proof.
    iSplit; simpl; first by case_decide; iDestruct 1 as (d' [= ->]) "$".
    iDestruct 1 as (->) "H"; rewrite decide_True //; naive_solver.
  Qed.
  Lemma lift_dty_dms_singleton_eq (TD : dltyO Σ) l ρ d :
    lift_dty_dms l TD ρ [(l, d)] ⊣⊢ TD ρ d.
  Proof.
    by rewrite lift_dty_dms_singleton_eq' pure_True // (left_id True%I bi_and).
  Qed.

  Definition lift_dty_vl `{!dlangG Σ} l (TD : dltyO Σ) : oltyO Σ 0 :=
    olty0 (λI ρ v, ∃ d, ⌜v @ l ↘ d ⌝ ∧ TD ρ d).
  Global Instance Proper_lift_dty_vl : Proper ((≡) ==> (≡)) (lift_dty_vl l).
  Proof. rewrite /lift_dty_vl => ???; simplify_eq; solve_proper_ho. Qed.

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
  Global Instance Proper_dty2clty l : Proper ((≡) ==> (≡)) (dty2clty l).
  Proof. split; rewrite /dty2clty/=; by repeat f_equiv. Qed.

  Lemma dty2clty_singleton l (TD : dlty Σ) ρ d :
    dty2clty l TD ρ [(l, d)] ≡ TD ρ d.
  Proof. by rewrite lift_dty_dms_singleton_eq. Qed.

  Definition lift_dty_vl_paper `{!dlangG Σ} (TD : dsltyO Σ) : oltyO Σ 0 := olty0 (λI ρ v,
    ∃ ds, ⌜v = vobj ds⌝ ∧ TD ρ (selfSubst ds)).

  Program Definition cTop : clty Σ := Clty (Dslty (λI _ _, True)) oTop.
  Solve All Obligations with eauto.

  Program Definition olty2clty `{!dlangG Σ} (U : oltyO Σ 0) : cltyO Σ :=
    Clty ⊥ U.
  Solve All Obligations with by iIntros.
  Global Instance : Bottom (clty Σ) := olty2clty ⊥.

  Program Definition cAnd (Tds1 Tds2 : clty Σ): clty Σ :=
    Clty (Dslty (λI ρ ds, Tds1 ρ ds ∧ Tds2 ρ ds)) (oAnd Tds1 Tds2).
  Next Obligation. intros. by rewrite /= -!clty_def2defs_head. Qed.
  Next Obligation. intros. by rewrite /= -!clty_mono. Qed.
  Next Obligation. intros. by rewrite /= -!clty_commute. Qed.
End DefsTypes.

Implicit Types (T: ty).

Class CTyInterp Σ :=
  clty_interp : ty → clty Σ.
(* Inspired by Autosubst. *)
Global Arguments clty_interp {_ _} !_ /.
Notation "C⟦ T ⟧" := (clty_interp T).

Notation "Ds⟦ T ⟧" := (clty_dslty C⟦ T ⟧).

(* We need [V⟦ _ ⟧] to be a proper first-class function. *)
Definition pty_interp `{CTyInterp Σ} T : oltyO Σ 0 := clty_olty C⟦ T ⟧.
Global Arguments pty_interp {_ _} !_ /.

Notation "V⟦ T ⟧" := (pty_interp T).
Notation "Vs⟦ g ⟧" := (fmap (M := gmap stamp) (B := hoEnvD _ 0) pty_interp g).
Notation "V⟦ Γ ⟧*" := (fmap (M := list) pty_interp Γ).

Class CTyInterpLemmas Σ `{!CTyInterp Σ} := {
  interp_subst_compose_ind T {args} ρ1 ρ2 v:
    V⟦ T.|[ρ1] ⟧ args ρ2 v ⊣⊢ V⟦ T ⟧ args (ρ1 >> ρ2) v;
}.

(** * Lemmas about the logical relation itself. *)
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
    V⟦ T.|[v/] ⟧ args ρ w ≡ V⟦ T ⟧ args (v.[ρ] .: ρ) w.
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
    rewrite interp_subst_compose_ind !(interp_subst_ids T _ _) -hsubst_comp.
    (* *The* step requiring [HclT]. *)
    by rewrite (subst_compose _ _ HclT).
  Qed.

  (** Substitution on semantic types commutes with the semantics. *)
  Lemma interp_subst_commute (T : ty) σ : V⟦ T.|[σ] ⟧ ≡ V⟦ T ⟧.|[σ].
  Proof. intros ???; apply interp_subst_compose_ind. Qed.
End logrel_binding_lemmas.
