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
Module clty_mixin.
  #[local] Set Primitive Projections.
  Record pred {Σ} (clty_dslty : dslty Σ) (clty_olty : oltyO Σ) : Prop := Mk {
    clty_def2defs_head {l d ds ρ} :
      clty_dslty ρ [(l, d)] ⊢ clty_dslty ρ ((l, d) :: ds);
    clty_mono {l d ds ρ} :
      dms_hasnt ds l →
      clty_dslty ρ ds ⊢ clty_dslty ρ ((l, d) :: ds);
    clty_commute {ds ρ} :
      clty_dslty ρ (selfSubst ds) ⊢ clty_olty anil ρ (vobj ds);
  }.
End clty_mixin.
Arguments clty_mixin.Mk {Σ _ _}.

Record clty {Σ} := _Clty {
  clty_dslty :> dslty Σ;
  (* Beware this coercion goes to [oltyO] not [olty], and it does not enable
  applying a [clty] to values; as visible in [olty_dlty2clty_eq], in that case
  it must still be used explicitly. *)
  clty_olty :> oltyO Σ;
  clty_mixin : clty_mixin.pred clty_dslty clty_olty;
}.
Add Printing Constructor clty.

Arguments clty : clear implicits.
Arguments _Clty {Σ}.
Notation Clty TD T := (_Clty TD T (clty_mixin.Mk _ _ _)).
Arguments clty_dslty {_} !_.
#[global] Instance : Params (@clty_dslty) 1 := {}.
Arguments clty_olty {_} !_.
#[global] Instance : Params (@clty_olty) 1 := {}.

Section clty_mixin'.
  Context {Σ} (c : clty Σ).

  Lemma clty_def2defs_head {l d ds ρ} :
    clty_dslty c ρ [(l, d)] ⊢ clty_dslty c ρ ((l, d) :: ds).
  Proof. apply /clty_mixin.clty_def2defs_head /clty_mixin. Qed.
  Lemma clty_mono {l d ds ρ} :
    dms_hasnt ds l →
    clty_dslty c ρ ds ⊢ clty_dslty c ρ ((l, d) :: ds).
  Proof. apply /clty_mixin.clty_mono /clty_mixin. Qed.
  Lemma clty_commute {ds ρ} :
    clty_dslty c ρ (selfSubst ds) ⊢ clty_olty c anil ρ (vobj ds).
  Proof. apply /clty_mixin.clty_commute /clty_mixin. Qed.
End clty_mixin'.

Section clty_ofe.
  Context {Σ}.

  Let clty_car : Type := (env -d> iPPredO dms Σ) * oltyO Σ.

  Let iso : clty Σ -> clty_car :=
    λ T : clty Σ, (clty_dslty T : _ -d> _, clty_olty T).
  #[local] Instance clty_equiv : Equiv (clty Σ) := λ A B, iso A ≡ iso B.
  #[local] Instance clty_dist : Dist (clty Σ) := λ n A B, iso A ≡{n}≡ iso B.
  Lemma clty_ofe_mixin : OfeMixin (clty Σ).
  Proof. exact: (iso_ofe_mixin iso). Qed.

  Canonical Structure cltyO := OfeT (clty Σ) clty_ofe_mixin.

  Let clty_pred : clty_car -> Prop := curry clty_mixin.pred.

  Let clty_pred_alt (c : clty_car) : Prop :=
    let dslty := fst c in
    let olty := snd c in
    (∀ l d ds ρ, dslty ρ [(l, d)] ⊢ dslty ρ ((l, d) :: ds)) ∧
    (∀ l d ds ρ, dms_hasnt ds l → dslty ρ ds ⊢ dslty ρ ((l, d) :: ds)) ∧
    (∀ ds ρ, dslty ρ (selfSubst ds) ⊢ olty anil ρ (vobj ds)).

  #[local] Instance : LimitPreserving clty_pred.
  Proof.
    apply (limit_preserving_ext clty_pred_alt). {
      move=> [dslty olty]; rewrite /clty_pred_alt /clty_pred; split => H.
      by destruct_and?.
      by destruct H.
    }
    repeat apply limit_preserving_and;
      repeat (apply limit_preserving_forall; intro);
      repeat apply limit_preserving_entails;
      move=> n [dslty1 olty1] [dslty2 olty2] [/= Hds Ho];
      first [apply Hds|apply Ho].
  Qed.

  #[global] Instance cofe_clty : Cofe cltyO.
  Proof.
    apply (iso_cofe_subtype' clty_pred (λ '(ds, o), _Clty ds o) iso).
    by case.
    by [].
    by case.
    apply _.
  Qed.
End clty_ofe.
Arguments cltyO : clear implicits.

Section clty_ofe_proper.
  Context {Σ}.

  #[global] Instance clty_olty_ne : NonExpansive (clty_olty (Σ := Σ)).
  Proof. by move=> ???[/= _ H]. Qed.
  #[global] Instance clty_olty_proper : Proper1 (clty_olty (Σ := Σ)) :=
    ne_proper _.

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
#[global] Instance : Params (@lift_dty_dms) 3 := {}.

Definition lift_dty_vl `{!dlangG Σ} l (TD : dltyO Σ) : oltyO Σ :=
  olty0 (λI ρ v, ∃ d, ⌜v @ l ↘ d ⌝ ∧ TD ρ d).
#[global] Instance : Params (@lift_dty_vl) 3 := {}.

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
  #[global] Instance lift_dty_dms_proper l : Proper1 (lift_dty_dms l) :=
    ne_proper _.

  #[global] Instance lift_dty_vl_ne l : NonExpansive (lift_dty_vl l).
  Proof. rewrite /lift_dty_vl => ??; simplify_eq; solve_proper_ho. Qed.
  #[global] Instance lift_dty_vl_proper l : Proper1 (lift_dty_vl l) :=
    ne_proper _.

  #[local] Arguments dms_lookup : simpl never.
  Lemma lift_dty_dms_head_intro (TD : dlty Σ) l1 l2 ρ d ds (Heq : l1 = l2) :
    TD ρ d -∗
    lift_dty_dms l1 TD ρ ((l2, d) :: ds).
  Proof. rewrite Heq /=. rewrite !dms_lookup_head. naive_solver. Qed.

  Lemma lift_dty_dms_singleton_eq' (TD : dlty Σ) l1 l2 ρ d :
    lift_dty_dms l1 TD ρ [(l2, d)] ⊣⊢ ⌜ l1 = l2 ⌝ ∧ TD ρ d.
  Proof.
    rewrite /lift_dty_dms; iSplit. {
      iDestruct 1 as (d' ?%dms_lookup_head_inv) "?". naive_solver.
    }
    iIntros "[-> ?]". by iApply lift_dty_dms_head_intro.
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

Section dty2clty.
  #[local] Arguments dms_lookup : simpl never.
  Program Definition dty2clty `{!dlangG Σ} l (T : dltyO Σ) : cltyO Σ :=
    Clty (lift_dty_dms l T) (lift_dty_vl l T).
  Next Obligation.
    intros. rewrite lift_dty_dms_singleton_eq' /=.
    iIntros "[<- ?] /=". rewrite dms_lookup_head. naive_solver.
  Qed.
  Next Obligation.
    iDestruct 1 as (d' ?) "?"; iExists d'.
    erewrite dms_lookup_mono => //. eauto.
  Qed.
  Next Obligation.
    intros. rewrite /lift_dty_dms /lift_dty_vl /=. f_equiv => d.
    iDestruct 1 as (Hl) "$". iIntros "!%". exact: objLookupIntro.
  Qed.
End dty2clty.
#[global] Instance : Params (@dty2clty) 3 := {}.

Section DefsTypes.
  Context `{HdotG : !dlangG Σ}.

  #[global] Instance olty2clty_ne : NonExpansive olty2clty.
  Proof. split; rewrite /=; by repeat f_equiv. Qed.
  #[global] Instance olty2clty_proper : Proper1 olty2clty :=
    ne_proper _.

  #[global] Instance dty2clty_ne l : NonExpansive (dty2clty l).
  Proof. split; rewrite /dty2clty/=; by repeat f_equiv. Qed.
  #[global] Instance dty2clty_proper l : Proper1 (dty2clty l) :=
    ne_proper _.

  Lemma dty2clty_singleton l (TD : dlty Σ) ρ d :
    dty2clty l TD ρ [(l, d)] ≡ TD ρ d.
  Proof. apply lift_dty_dms_singleton_eq. Qed.

  Definition olty_dlty2clty_eq l (TD : dlty Σ) ρ v :
    clty_olty (dty2clty l TD) anil ρ v ⊣⊢ lift_dty_vl l TD anil ρ v := reflexivity _.

  Program Definition cTop : clty Σ := Clty (Dslty (λI _ _, True)) oTop.
  Solve All Obligations with eauto.

  #[global] Instance clty_bottom : Bottom (clty Σ) := olty2clty ⊥.
  #[global] Instance clty_inh : Inhabited (clty Σ) := populate ⊥.

  Program Definition cAnd (Tds1 Tds2 : clty Σ) : clty Σ :=
    Clty (Dslty (λI ρ ds, Tds1 ρ ds ∧ Tds2 ρ ds)) (oAnd Tds1 Tds2).
  Next Obligation. intros. by rewrite /= -!clty_def2defs_head. Qed.
  Next Obligation. intros. by rewrite /= -!clty_mono. Qed.
  Next Obligation. intros. by rewrite /= -!clty_commute. Qed.

  #[global] Instance cAnd_ne : NonExpansive2 cAnd.
  Proof. split; rewrite /=; repeat f_equiv; solve_proper_ho. Qed.
  #[global] Instance cAnd_proper : Proper2 cAnd :=
    ne_proper_2 _.

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

Definition RecTyInterp Σ : Type := ty -d> hoEnvD Σ.
Existing Class RecTyInterp.
Typeclasses Transparent RecTyInterp.

(** When a definition points to a semantic type. Inlined in paper. *)
Definition dm_to_type `{HdotG : !dlangG Σ} d (ψ : hoD Σ) {rinterp : RecTyInterp Σ} : iProp Σ :=
  match d with
  | dtysem σ s => s ↗n[ σ ] ψ
  | dtysyn T => ▷ (∀ args, ψ args ≡ rinterp T args ids)
  | dpt _ => False
  end.
#[global] Instance dm_to_type_ne `{HdotG : !dlangG Σ} d n :
  Proper (dist_later n ==> dist_later n ==> dist n) (dm_to_type d).
Proof. solve_contractive_ho. Qed.

Notation "d ↗ ψ" := (dm_to_type d ψ) (at level 20).

Section dm_to_type.
  Context `{HdotG : !dlangG Σ} `{rinterp : !RecTyInterp Σ}.

  Lemma dm_to_type_agree {d ψ1 ψ2} args v : d ↗ ψ1 -∗ d ↗ ψ2 -∗ ▷ (ψ1 args v ≡ ψ2 args v).
  Proof.
    destruct d; simpl; [ | apply stamp_σ_to_type_agree | by iIntros "[]" ].
    iIntros "H1 H2 !>"; iRewrite ("H1" $! args); iRewrite ("H2" $! args). by [].
  Qed.

  Lemma dm_to_type_intro d s σ φ :
    d = dtysem σ s → s ↝n φ -∗ d ↗ hoEnvD_inst σ φ.
  Proof. move=>->/=. apply stamp_σ_to_type_intro. Qed.

  Lemma dm_to_type_syn_intro d T :
    d = dtysyn T → ⊢ d ↗ (λ args, rinterp T args ids).
  Proof. move->. by iIntros "!>". Qed.

  #[global] Opaque dm_to_type.
End dm_to_type.
