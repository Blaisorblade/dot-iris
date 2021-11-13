(** * Semantic domains for DOT logical relations. *)
From iris.proofmode Require Import tactics.
From D Require Export iris_prelude proper lty lr_syn_aux.
From D.Dot Require Import syn.
From D.Dot Require Export dlang_inst path_wp.

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
Instance : Params (@clty_dslty) 1 := {}.
Arguments clty_olty {_} !_.
Instance : Params (@clty_olty) 1 := {}.

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
Instance : Params (@lift_dty_dms) 3 := {}.

Definition lift_dty_vl `{!dlangG Σ} l (TD : dltyO Σ) : oltyO Σ :=
  olty0 (λI ρ v, ∃ d, ⌜v @ l ↘ d ⌝ ∧ TD ρ d).
Instance : Params (@lift_dty_vl) 3 := {}.

(** This definition is only useful to show in [lift_dty_vl_equiv_paper] that
certain definitions we give are equivalent to the ones in the paper. *)
Definition lift_dty_vl_paper `{!dlangG Σ} (TD : dsltyO Σ) : oltyO Σ := olty0 (λI ρ v,
  ∃ ds, ⌜v = vobj ds⌝ ∧ TD ρ (selfSubst ds)).

Section lift_dty_lemmas.
  Context `{HdotG : !dlangG Σ}.

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
#[global] Instance : Params (@olty2clty) 2 := {}.

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
#[global] Instance : Params (@dty2clty) 3 := {}.

Section DefsTypes.
  Context `{HdotG : !dlangG Σ}.

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

  Program Definition cAnd (Tds1 Tds2 : clty Σ) : clty Σ :=
    Clty (Dslty (λI ρ ds, Tds1 ρ ds ∧ Tds2 ρ ds)) (oAnd (c2o Tds1) (c2o Tds2)).
  Next Obligation. intros. by rewrite /= -!clty_def2defs_head. Qed.
  Next Obligation. intros. by rewrite /= -!clty_mono. Qed.
  Next Obligation. intros. by rewrite /= -!clty_commute. Qed.

  #[global] Instance cAnd_ne : NonExpansive2 cAnd.
  Proof. split; rewrite /=; repeat f_equiv; solve_proper_ho. Qed.
  #[global] Instance cAnd_proper :
    Proper ((≡) ==> (≡) ==> (≡)) cAnd := ne_proper_2 _.

  Lemma cAnd_olty2clty T1 T2 :
    cAnd (olty2clty T1) (olty2clty T2) ≡ olty2clty (oAnd T1 T2).
  Proof. split=>??//=. apply: left_absorb. Qed.

  Lemma cAnd_cTop T : cAnd T cTop ≡@{clty Σ} T.
  Proof.
    split; [intros ρ ds | intros args ρ v]; apply: (right_id _ bi_and).
  Qed.
End DefsTypes.

#[global] Instance : Params (@cAnd) 1 := {}.

Implicit Types (T : ty).

(** * Constructions on gDOT semantic types. *)
(** ** Semantic path substitution and replacement. *)

(** Semantic substitution of path in type. *)
Definition opSubst `{!dlangG Σ} p (T : oltyO Σ) : oltyO Σ :=
  Olty (λI args ρ v, path_wp p.|[ρ] (λ w, T args (w .: ρ) v)).
Notation "T .sTp[ p /]" := (opSubst p T) (at level 65).

(** Semantic definition of path replacement. *)
Definition sem_ty_path_replI {Σ} p q (T1 T2 : olty Σ) : iProp Σ :=
  |==> ∀ args ρ v (Hal : alias_paths p.|[ρ] q.|[ρ]), T1 args ρ v ≡ T2 args ρ v.
(* sTpI = semantic Type Path Iris; matches [sem_kind_path_replI] *)
Notation "T1 ~sTpI[ p := q  ]* T2" :=
  (sem_ty_path_replI p q T1 T2) (at level 70).

(** Semantic definition of path replacement: alternative, weaker version.
Unlike [sem_ty_path_replI], this version in [Prop] is less expressive, but
sufficient for our goals and faster to use in certain proofs. *)
Definition sem_ty_path_repl {Σ} p q (T1 T2 : olty Σ) : Prop :=
  ∀ args ρ v, alias_paths p.|[ρ] q.|[ρ] → T1 args ρ v ≡ T2 args ρ v.
(* sTpI = semantic Type Path Prop; matches [sem_kind_path_repl] *)
Notation "T1 ~sTpP[ p := q  ]* T2" :=
  (sem_ty_path_repl p q T1 T2) (at level 70).

Section path_repl.
  Context `{!dlangG Σ}.

  Lemma opSubst_pv_eq v (T : oltyO Σ) : T .sTp[ pv v /] ≡ T.|[v/].
  Proof. move=> args ρ w /=. by rewrite path_wp_pv_eq subst_swap_base. Qed.

  Lemma sem_psubst_one_repl {T : olty Σ} {args p v w ρ} :
    alias_paths p.|[ρ] (pv v) →
    T .sTp[ p /] args ρ w ≡ T args (v .: ρ) w.
  Proof. move=> /alias_paths_elim_eq /= ->. by rewrite path_wp_pv_eq. Qed.

  Lemma sem_ty_path_repl_eq {p q} {T1 T2 : olty Σ} :
    T1 ~sTpP[ p := q ]* T2 → ⊢ T1 ~sTpI[ p := q ]* T2.
  Proof. iIntros "%Heq !% /=". apply: Heq. Qed.
  (* The reverse does not hold. *)
End path_repl.

(** When a definition points to a semantic type. Inlined in paper. *)
Definition dm_to_type `{HdotG : !dlangG Σ} d (ψ : hoD Σ) : iProp Σ :=
  ∃ s σ, ⌜ d = dtysem σ s ⌝ ∧ s ↗n[ σ ] ψ.
Notation "d ↗n ψ" := (dm_to_type d ψ) (at level 20).

Section dm_to_type.
  Context `{HdotG : !dlangG Σ}.

  Lemma dm_to_type_agree {d ψ1 ψ2} args v : d ↗n ψ1 -∗ d ↗n ψ2 -∗ ▷ (ψ1 args v ≡ ψ2 args v).
  Proof.
    iDestruct 1 as (s σ ?) "#Hs1".
    iDestruct 1 as (s' σ' ?) "#Hs2".
    simplify_eq. by iApply (stamp_σ_to_type_agree args with "Hs1 Hs2").
  Qed.

  Lemma dm_to_type_intro d s σ φ :
    d = dtysem σ s → s ↝n φ -∗ d ↗n hoEnvD_inst σ φ.
  Proof.
    iIntros. iExists s, σ. iFrame "%".
    by iApply stamp_σ_to_type_intro.
  Qed.

  #[global] Opaque dm_to_type.
End dm_to_type.
