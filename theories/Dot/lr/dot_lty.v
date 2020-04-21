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

(** The semantics of a DOT type as a single-definition type is a pair of an
expected label (if any) and a persistent predicate over the definition. *)
Record ldlty Σ := LDlty {
  ldlty_label : option label;
  ldlty_car :> env → iPPred dm Σ;
}.
Add Printing Constructor ldlty.
Global Arguments LDlty {_} _%I _.
Global Arguments ldlty_label {_} !_ /.
Global Arguments ldlty_car {_} !_ /.

Canonical Structure labelO := leibnizO label.

(** Semantic definition types [ldlty Σ] can be converted (through [lift_ldlty], below)
into persistent predicates over labels and definitions of the following type. *)
Definition dlty Σ := env → label → iPPred dm Σ.
Definition dltyO Σ := env -d> label -d> iPPredO dm Σ.
Notation Dlty T := (λ ρ l, IPPred (λI d, T ρ l d)).

Section ldlty_ofe.
  Context {Σ}.
  Let iso := (λ T : ldlty Σ, (ldlty_car T : _ -d> _, ldlty_label T)).
  Instance ldlty_equiv : Equiv (ldlty Σ) := λ A B, iso A ≡ iso B.
  Instance ldlty_dist : Dist (ldlty Σ) := λ n A B, iso A ≡{n}≡ iso B.
  Lemma ldlty_ofe_mixin : OfeMixin (ldlty Σ).
  Proof. exact: (iso_ofe_mixin iso). Qed.

  Canonical Structure ldltyO := OfeT (ldlty Σ) ldlty_ofe_mixin.

  (* Looks trivial, but it's needed for its Proper instance. *)
  Definition LDltyO ol (P : env -d> iPPredO dm Σ) : ldltyO := LDlty ol P.
  Global Instance Proper_LDltyO: Proper ((≡) ==> (≡)) (LDltyO ol).
  Proof. by solve_proper_prepare. Qed.

  Definition mkLDlty ol (φ : envPred dm Σ) `{∀ ρ d, Persistent (φ ρ d)} :=
    LDltyO ol (λ ρ, IPPred (φ ρ)).
  Global Arguments mkLDlty /.

  Global Instance : Bottom (ldlty Σ) := mkLDlty None ⊥.

  Definition lift_ldlty (TD : ldltyO) : dltyO Σ := Dlty (λI ρ l' d,
    match ldlty_label TD with
    | None => ⊥
    | Some l => ⌜ l = l' ⌝ ∧ TD ρ d
    end).
End ldlty_ofe.
Arguments ldltyO : clear implicits.
Global Arguments lift_ldlty {_} _ /.

Notation dslty Σ := (env → iPPred dms Σ).
Definition dsltyO Σ := env -d> iPPredO dms Σ.
Notation Dslty T := (λ ρ, IPPred (λI ds, T ρ ds)).

(** A "complete" logical type, containing all semantics of a type — for
definition lists, single definitions, and values; together with proofs that
they agree appropriately. *)
Record clty {Σ} := Clty {
  clty_dslty :> dslty Σ;
  clty_dlty : ldltyO Σ;
  clty_olty :> oltyO Σ 0;
  clty_def2defs_head {l d ds ρ} :
    lift_ldlty clty_dlty ρ l d ⊢ clty_dslty ρ ((l, d) :: ds);
  clty_mono {l d ds ρ} :
    dms_hasnt ds l →
    clty_dslty ρ ds ⊢ clty_dslty ρ ((l, d) :: ds);
  clty_commute {ds ρ} :
    clty_dslty ρ (selfSubst ds) ⊢ clty_olty vnil ρ (vobj ds);
}.
Add Printing Constructor clty.

Arguments clty : clear implicits.
Arguments Clty {_} _ _ _ _ _.
Arguments clty_dslty {_} !_ /.
Arguments clty_olty {_} !_ /.
Arguments clty_dlty {_} !_ /.

Section clty_ofe.
  Context {Σ}.

  Let iso := (λ T : clty Σ, (clty_dslty T : _ -d> _, clty_dlty T, clty_olty T)).
  Instance clty_equiv : Equiv (clty Σ) := λ A B, iso A ≡ iso B.
  Instance clty_dist : Dist (clty Σ) := λ n A B, iso A ≡{n}≡ iso B.
  Lemma clty_ofe_mixin : OfeMixin (clty Σ).
  Proof. exact: (iso_ofe_mixin iso). Qed.
End clty_ofe.
Canonical Structure cltyO Σ := OfeT (clty Σ) clty_ofe_mixin.

Section DefsTypes.
  Context `{HdotG: dlangG Σ}.

  Definition lift_dinterp_vl (TD : ldltyO Σ) : oltyO Σ 0 := olty0 (λI ρ v,
    match ldlty_label TD with
    | None => ⊥
    | Some l => ∃ d, ⌜v @ l ↘ d⌝ ∧ TD ρ d
    end).
  Global Instance Proper_lift_dinterp_vl : Proper ((≡) ==> (≡)) lift_dinterp_vl.
  Proof.
    rewrite /lift_dinterp_vl => ??[/=??]; repeat case_match;
      simplify_eq; solve_proper_ho.
  Qed.

  Definition lift_dinterp_dms `{dlangG Σ} (TD : ldltyO Σ) : dsltyO Σ := Dslty (λI ρ ds,
    ∃ l d, ⌜ dms_lookup l ds = Some d ⌝ ∧ lift_ldlty TD ρ l d).
  Global Instance Proper_lift_dinterp_dms : Proper ((≡) ==> (≡)) lift_dinterp_dms.
  Proof.
    rewrite /lift_dinterp_dms/= => ?? [/=??] ??/=;
      repeat case_match; simplify_eq/=; solve_proper_ho.
  Qed.

  Program Definition ldlty2clty `{dlangG Σ} (T : ldltyO Σ) : cltyO Σ :=
    Clty (lift_dinterp_dms T) T (lift_dinterp_vl T) _ _ _.
  Next Obligation.
    iIntros "* /= H"; case_match; last done.
    iExists l, d; iFrame. iIntros "!%". exact: dms_lookup_head.
  Qed.
  Next Obligation.
    intros; cbn; case_match; iDestruct 1 as (l' d' ?) "H /="; last done.
    iExists l', d'; iFrame; iIntros "!%". exact: dms_lookup_mono.
  Qed.
  Next Obligation.
    intros; rewrite /lift_dinterp_vl /=; case_match;
      iDestruct 1 as (?l' d ?) "H"; last done.
    iExists d; iDestruct "H" as (->) "$"; iIntros "!%". naive_solver.
  Qed.

  Global Instance Proper_ldlty2clty : Proper ((≡) ==> (≡)) ldlty2clty.
  Proof.
    rewrite /ldlty2clty => ???; split=>/=; repeat f_equiv; solve_proper.
  Qed.

  Program Definition cTop : clty Σ := Clty (Dslty (λI _ _, True)) ⊥ oTop _ _ _.
  Solve All Obligations with eauto.

  Program Definition olty2clty `{dlangG Σ} (U : oltyO Σ 0) : cltyO Σ :=
    Clty ⊥ ⊥ U _ _ _.
  Solve All Obligations with by iIntros.
  Global Instance : Bottom (clty Σ) := olty2clty ⊥.

  Program Definition cAnd (Tds1 Tds2 : clty Σ): clty Σ :=
    Clty (Dslty (λI ρ ds, Tds1 ρ ds ∧ Tds2 ρ ds)) ⊥ (oAnd Tds1 Tds2) _ _ _.
  Next Obligation. intros; iIntros "[]". Qed.
  Next Obligation. intros; iIntros "/= [??]". iSplit; by iApply clty_mono. Qed.
  Next Obligation. intros; iIntros "/= [??]". iSplit; by iApply clty_commute. Qed.
End DefsTypes.

Implicit Types (T: ty).

Class CTyInterp Σ :=
  clty_interp : ty → clty Σ.
(* Inspired by Autosubst. *)
Global Arguments clty_interp {_ _} !_ /.
Notation "C⟦ T ⟧" := (clty_interp T).

Notation "Ds⟦ T ⟧" := (clty_dslty C⟦ T ⟧).
Notation "LD⟦ T ⟧" := (clty_dlty C⟦ T ⟧).

(* We need [V⟦ _ ⟧] to be a proper first-class function. *)
Definition pty_interp `{CTyInterp Σ} T : oltyO Σ 0 := clty_olty C⟦ T ⟧.
Global Arguments pty_interp {_ _} !_ /.

Notation "V⟦ T ⟧" := (pty_interp T).
Notation "Vs⟦ g ⟧" := (fmap (M := gmap stamp) (B := hoEnvD _ 0) pty_interp g).
Notation "V⟦ Γ ⟧*" := (fmap (M := list) pty_interp Γ).

Definition def_interp `{CTyInterp Σ} T l ρ d := lift_ldlty LD⟦ T ⟧ ρ l d.
Notation "D[ l ]⟦ T ⟧" := (def_interp T l).

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
