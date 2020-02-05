From iris.proofmode Require Import tactics.
From D Require Export iris_prelude proper lty lr_syn_aux.
From D.Dot Require Import syn.
From D.Dot Require Export dlang_inst.

(** * Semantic domains for DOT logical relations. *)

Unset Program Cases.

Implicit Types (Σ : gFunctors)
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (vs : vls) (ρ : var → vl) (l : label).

Include Lty VlSorts dlang_inst.

Section bottoms.
  Context {Σ}.
  Global Instance bottom_iprop : Bottom (iProp Σ) := False%I.
  Global Instance bottom_ippred {s}: Bottom (iPPred s Σ) := IPPred (λ _, ⊥).
  Global Instance bottom_fun {A} `{Bottom B}: Bottom (A → B) := (λ _, ⊥).
  Global Instance bottom_ofe_fun {A} {B : ofeT} `{Bottom B}: Bottom (A -d> B) := (λ _, ⊥).
End bottoms.

(** The semantics of a DOT type as a single-definition type is a pair of an
expected label (if any) and a persistent predicate over the definition. *)
Record ldlty Σ := LDlty {
  ldlty_label : option label;
  ldlty_car :> env -> iPPred dm Σ;
}.
Global Arguments LDlty {_} _%I _.
Global Arguments ldlty_label {_} !_ /.
Global Arguments ldlty_car {_} !_ /.

Canonical Structure labelO := leibnizO label.

(** Semantic definition types [ldlty Σ] can be converted (through [lift_ldlty], below)
into persistent predicates over labels and definitions of the following type. *)
Definition dlty Σ := env -> label -> iPPred dm Σ.
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
  Global Arguments lift_ldlty /.

  Global Instance Proper_lift_ldlty : Proper ((≡) ==> (≡)) lift_ldlty.
  Proof.
    move => [l1 P1] [l2 P2] [/= Heq Heql]; repeat case_match; simplify_eq/=;
      solve_proper_ho.
  Qed.
End ldlty_ofe.
Arguments ldltyO : clear implicits.
Global Instance: Params (@lift_ldlty) 5 := {}.

Notation dslty Σ := (env -> iPPred dms Σ).
Definition dsltyO Σ := env -d> iPPredO dms Σ.
Notation Dslty T := (λ ρ, IPPred (λI ds, T ρ ds)).

(** All semantics of a type. *)
Record ldslty {Σ} := LDslty {
  ldslty_car :> dslty Σ;
  ldslty_olty : oltyO Σ 0;
  ldslty_dlty : ldltyO Σ;
  ldslty_commute {ds ρ} :
    ldslty_car ρ (selfSubst ds) ⊢ ldslty_olty vnil ρ (vobj ds);
  ldslty_mono {l d ds ρ} :
    dms_hasnt ds l →
    ldslty_car ρ ds ⊢ ldslty_car ρ ((l, d) :: ds);
  ldslty_def2defs_head {l d ds ρ} :
    lift_ldlty ldslty_dlty ρ l d ⊢ ldslty_car ρ ((l, d) :: ds)
}.

Arguments ldslty : clear implicits.
Arguments LDslty {_} _ _ _ _ _.
Arguments ldslty_car {_} !_ /.
Arguments ldslty_olty {_} !_ /.
Arguments ldslty_dlty {_} !_ /.

Section ldslty_ofe.
  Context {Σ}.

  Let iso := (λ T : ldslty Σ, (ldslty_car T : _ -d> _, ldslty_olty T, ldslty_dlty T)).
  Instance ldslty_equiv : Equiv (ldslty Σ) := λ A B, iso A ≡ iso B.
  Instance ldslty_dist : Dist (ldslty Σ) := λ n A B, iso A ≡{n}≡ iso B.
  Lemma ldslty_ofe_mixin : OfeMixin (ldslty Σ).
  Proof. exact: (iso_ofe_mixin iso). Qed.
End ldslty_ofe.
Canonical Structure ldsltyO Σ := OfeT (ldslty Σ) ldslty_ofe_mixin.

Section DefsTypes.
  Context `{HdotG: dlangG Σ}.

  Program Definition lift_dinterp_vl (TD : ldltyO Σ) : oltyO Σ 0 := olty0 (λI ρ v,
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

  Program Definition ldlty2ldslty `{dlangG Σ} (T : ldltyO Σ) : ldsltyO Σ :=
    LDslty (lift_dinterp_dms T) (lift_dinterp_vl T) T _ _ _.
  Next Obligation.
    intros; rewrite /lift_dinterp_vl /=; case_match;
      iDestruct 1 as (?l' d ?) "H"; last done.
    iExists d; iDestruct "H" as (->) "$".
    iIntros "!%"; naive_solver.
  Qed.
  Next Obligation.
    intros; cbn; case_match; iDestruct 1 as (l' d' ?) "H /="; last done.
    iExists l', d'; iFrame; iIntros "!%".
    exact: dms_lookup_mono.
  Qed.
  Next Obligation.
    (* iIntros "* /="; case_match; simplify_eq/=; last done. *)
    iIntros "* /= H". case_match; last done.
    iExists l, d; iFrame. iIntros "!%".
    exact: dms_lookup_head.
  Qed.

  Program Definition LDsTop : ldslty Σ := LDslty (Dslty (λI _ _, True)) oTop ⊥ _ _ _.
  Solve All Obligations with eauto.

  Program Definition olty2ldslty `{dlangG Σ} (T : oltyO Σ 0) : ldsltyO Σ :=
    LDslty ⊥ T ⊥ _ _ _.
  Solve All Obligations with by iIntros.
  Global Instance : Bottom (ldslty Σ) := olty2ldslty ⊥.

  Program Definition LDsAnd (Tds1 Tds2 : ldslty Σ): ldslty Σ :=
    LDslty (Dslty (λI ρ ds, Tds1 ρ ds ∧ Tds2 ρ ds)) (oAnd (ldslty_olty Tds1) (ldslty_olty Tds2)) ⊥ _ _ _.
  Next Obligation. intros; iIntros "/= [??]". iSplit; by iApply ldslty_commute. Qed.
  Next Obligation. intros; iIntros "/= [??]". iSplit; by iApply ldslty_mono. Qed.
  Next Obligation. intros; iIntros "[]". Qed.

End DefsTypes.

Class PTyInterp ty Σ :=
  pty_interpO : ty -> oltyO Σ 0.
Notation "V⟦ T ⟧" := (pty_interpO T).

(* Also appears in Autosubst. *)
Global Arguments pty_interpO {_ _ _} !_ /.

Definition pty_interp `{PTyInterp ty Σ} : ty -> hoEnvD Σ 0 := pty_interpO.
Notation "Vs⟦ g ⟧" := (fmap (M := gmap stamp) pty_interp g).
Global Arguments pty_interp /.

Class PTyInterpLemmas ty Σ `{sort_ty : Sort ty} `{!PTyInterp ty Σ} := {
  interp_subst_compose_ind T {args} ρ1 ρ2 v:
    V⟦ T.|[ρ1] ⟧ args ρ2 v ⊣⊢ V⟦ T ⟧ args (ρ1 >> ρ2) v;
}.

(** * Lemmas about the logical relation itself. *)
Section logrel_binding_lemmas.
  Context `{Htil : PTyInterpLemmas ty Σ}.

  Implicit Types (T: ty).

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
  Lemma interp_subst_commute T σ ρ v (HclT : nclosed T (length σ)) args :
    V⟦ T.|[∞ σ] ⟧ args ρ v ≡ V⟦ T ⟧ args (∞ σ.|[ρ]) v.
  Proof.
    rewrite interp_subst_compose_ind !(interp_subst_ids T _ _) -hsubst_comp.
    (* *The* step requiring [HclT]. *)
    by rewrite (subst_compose _ _ HclT).
  Qed.
End logrel_binding_lemmas.
