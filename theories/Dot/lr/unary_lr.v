From iris.proofmode Require Import tactics.
From D Require Export iris_prelude proper lty lr_syn_aux.
From D Require Import pty_interp_subst_lemmas swap_later_impl.
From D.Dot Require Import syn syn.path_repl.
From D.Dot Require Export dlang_inst path_wp.
From D.pure_program_logic Require Import lifting.

Unset Program Cases.

Implicit Types (Σ : gFunctors)
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (vs : vls) (ρ : var → vl) (l : label).

(** * Semantic domains. *)

Include Lty VlSorts dlang_inst.
Include PTyInterpLemmas VlSorts dlang_inst.
Export persistent_ty_interp_lemmas.

Section bottoms.
  Context {Σ}.
  Global Instance bottom_iprop : Bottom (iProp Σ) := False%I.
  Global Instance bottom_ippred {s}: Bottom (iPPred s Σ) := IPPred (λ _, ⊥).
  Global Instance bottom_fun {A} `{Bottom B}: Bottom (A → B) := (λ _, ⊥).
  Global Instance bottom_ofe_fun {A} {B : ofeT} `{Bottom B}: Bottom (A -d> B) := (λ _, ⊥).
End bottoms.

(** The logical relation core is [V⟦T⟧], which interprets *open* types into
    predicates over *closed* values. Hence, [V⟦T⟧ T args ρ v] uses its argument [ρ]
    to interpret anything contained in T, but not things contained in v.

    Semantic judgements must apply instead to open terms/value/paths; therefore,
    they are defined using closing substitution on arguments of [interp].

    Similar comments apply to [def_interp].

    Additionally, both apply to *stamped* syntax, hence they only expect
    [dtysem] and not [dtysyn] for type member definitions.
 *)

(** Override notations to specify scope. *)
Notation "V⟦ T ⟧" := (pty_interpO T%ty).

Notation "V⟦ Γ ⟧*" := (fmap (M := list) pty_interpO Γ).

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
      solve_proper_ho_equiv.
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

(** Define fully semantic judgments. They accept arbitrary semantic types. *)

Section judgments.
  Context {Σ}.
  Implicit Types (τ : oltyO Σ 0).

  (** How do we represent subtyping in a later world? We have two distinct
      choices, because in Iris ▷(P ⇒ Q) ⊢ ▷ P ⇒ ▷ Q but not viceversa
      (unlike with raw step-indexing).
      In turn, that's because to show ▷ P ⇒ ▷ Q we can assume resources are
      valid one step earlier, unlike for ▷(P ⇒ Q).

      It seems easier, in subtyping judgment, to use the weaker choice: that is,
      just delay individual types via (Γ ⊨ TLater T <: TLater U), that is

      (□∀ ρ v, G⟦Γ⟧ ρ → ▷ V⟦T1⟧ ρ v → ▷ V⟦T2⟧ ρ v),

      instead of instead of introducing some notation to write

      (□∀ ρ v, G⟦Γ⟧ ρ → ▷ (V⟦T1⟧ ρ v → V⟦T2⟧ ρ v)).

      And that forces using the same implication in the logical relation
      (unlike I did originally). *)

  (** Expression typing *)
  Definition setp `{dlangG Σ} e Γ τ : iProp Σ :=
    □∀ ρ, s⟦Γ⟧* ρ → E⟦ τ ⟧ ρ (e.|[ρ]).
  Global Arguments setp /.

  (** Indexed subtyping. *)
  Definition sstpi `{dlangG Σ} i j Γ τ1 τ2 : iProp Σ :=
    □∀ ρ v,
      s⟦Γ⟧*ρ → ▷^i oClose τ1 ρ v → ▷^j oClose τ2 ρ v.
  Global Arguments sstpi /.

  (** Definition typing *)
  Definition sdtp `{dlangG Σ} l d Γ (φ : ldltyO Σ): iProp Σ :=
    □∀ ρ, ⌜path_includes (pv (ids 0)) ρ [(l, d)] ⌝ → s⟦Γ⟧* ρ → lift_ldlty φ ρ l d.|[ρ].
  Global Arguments sdtp /.

  (** Multi-definition typing *)
  Definition sdstp `{dlangG Σ} ds Γ (T : dsltyO Σ) : iProp Σ :=
    ⌜wf_ds ds⌝ ∧ □∀ ρ, ⌜path_includes (pv (ids 0)) ρ ds ⌝ → s⟦Γ⟧* ρ → T ρ ds.|[ρ].
  Global Arguments sdstp /.

  (** Path typing *)
  Definition sptp `{dlangG Σ} p i Γ (T : oltyO Σ 0): iProp Σ :=
    □∀ ρ, s⟦Γ⟧* ρ -∗
      ▷^i path_wp (p.|[ρ]) (λ v, oClose T ρ v).
  Global Arguments sptp /.
End judgments.

(** Expression typing *)
Notation "Γ s⊨ e : τ" := (setp e Γ τ) (at level 74, e, τ at next level).
(** Indexed subtyping *)
Notation "Γ s⊨ T1 , i <: T2 , j " := (sstpi i j Γ T1 T2) (at level 74, T1, T2, i, j at next level).
(** Single-definition typing *)
Notation "Γ s⊨ {  l := d  } : T" := (sdtp l d Γ T) (at level 64, d, l, T at next level).
(** Multi-definition typing *)
Notation "Γ s⊨ds ds : T" := (sdstp ds Γ T) (at level 74, ds, T at next level).
(** Path typing *)
Notation "Γ s⊨p p : τ , i" := (sptp p i Γ τ) (at level 74, p, τ, i at next level).

Definition dm_to_type `{HdotG: dlangG Σ} d i (ψ : hoD Σ i) : iProp Σ :=
  (∃ s σ, ⌜ d = dtysem σ s ⌝ ∧ s ↗n[ σ , i ] ψ)%I.
Notation "d ↗n[ i  ] ψ" := (dm_to_type d i ψ) (at level 20).

Section dm_to_type.
  Context `{HdotG: dlangG Σ}.

  Global Instance dm_to_type_persistent d i ψ: Persistent (d ↗n[ i ] ψ) := _.

  Lemma dm_to_type_agree {d i ψ1 ψ2} args v : d ↗n[ i ] ψ1 -∗ d ↗n[ i ] ψ2 -∗ ▷ (ψ1 args v ≡ ψ2 args v).
  Proof.
    iDestruct 1 as (s σ ?) "#Hs1".
    iDestruct 1 as (s' σ' ?) "#Hs2".
    simplify_eq. by iApply (stamp_σ_to_type_agree args with "Hs1 Hs2").
  Qed.

  Lemma dm_to_type_intro d i s σ φ :
    d = dtysem σ s → s ↝n[ i ] φ -∗ d ↗n[ i ] hoEnvD_inst σ φ.
  Proof.
    iIntros. iExists s, σ. iFrame "%".
    by iApply stamp_σ_to_type_intro.
  Qed.

  Definition dm_to_type_eq d i ψ : dm_to_type d i ψ =
    (∃ s σ, ⌜ d = dtysem σ s ⌝ ∧ s ↗n[ σ , i ] ψ)%I := eq_refl.

  Global Opaque dm_to_type.
End dm_to_type.

Section SemTypes.
  Context `{HdotG: dlangG Σ}.

  Implicit Types (τ : oltyO Σ 0).
   (* (ψ : vl -d> iPropO Σ) (φ : envD Σ)  *)

  (* Rewrite using (higher) semantic kinds! *)
  Definition oLDTMem l τ1 τ2 : ldltyO Σ := mkLDlty (Some l) (λI ρ d,
    ∃ ψ, d ↗n[ 0 ] ψ ∧
       □ ((∀ v, ▷ τ1 vnil ρ v → ▷ □ ψ vnil v) ∧
          (∀ v, ▷ □ ψ vnil v → ▷ τ2 vnil ρ v))).
  Global Instance Proper_oLDTMem l : Proper ((≡) ==> (≡) ==> (≡)) (oLDTMem l).
  Proof. rewrite /oLDTMem/= => ??? ???. f_equiv. solve_proper_ho_equiv. Qed.

  Definition oLDVMem l τ : ldltyO Σ := mkLDlty (Some l) (λI ρ d,
    ∃ pmem, ⌜d = dpt pmem⌝ ∧ path_wp pmem (oClose τ ρ)).
  Global Instance Proper_oLDVMem l : Proper ((≡) ==> (≡)) (oLDVMem l).
  Proof. rewrite /oLDVMem/= => ???. f_equiv. solve_proper_ho_equiv. Qed.

  Definition oSel {i} p l : oltyO Σ i :=
    Olty (λI args ρ v, path_wp p.|[ρ]
      (λ vp, ∃ ψ d, ⌜vp @ l ↘ d⌝ ∧ d ↗n[ i ] ψ ∧ ▷ □ ψ args v)).

  Lemma oSel_pv {i} w l args ρ v :
    oSel (pv w) l args ρ v ⊣⊢
      ∃ ψ d, ⌜w.[ρ] @ l ↘ d⌝ ∧ d ↗n[ i ] ψ ∧ ▷ □ ψ args v.
  Proof. by rewrite /= path_wp_pv. Qed.

  Definition oSing `{dlangG Σ} p : olty Σ 0 := olty0 (λI ρ v, ⌜alias_paths p.|[ρ] (pv v)⌝).

  (* Paolo: This definition is contractive (similarly to what's useful for
     equi-recursive types).
     However, I am not sure we need this; it'd be good to
     write an example where this makes a difference.
     I think that would be something like
     nu x. { T = TNat; U = x.T -> x.T }:
     mu (x: {T <: TNat; U <: x.T -> TNat}).
     If the function type constructor is not contractive but only non-expansive,
     typechecking this example needs to establish x.T <: TNat having in context
     only x: {T <: TNat; U <: x.T -> TNat}.
   *)
  Definition oAll τ1 τ2 := olty0
    (λI ρ v,
    (∃ t, ⌜ v = vabs t ⌝ ∧
     □ ∀ w, ▷ τ1 vnil ρ w → ▷ E⟦ τ2 ⟧ (w .: ρ) t.|[w/])).

  Global Instance Proper_oAll : Proper ((≡) ==> (≡) ==> (≡)) oAll.
  Proof. solve_proper_ho_equiv. Qed.

  Definition oPrim b : olty Σ 0 := olty0 (λI ρ v, ⌜pure_interp_prim b v⌝).

  Program Definition lift_dinterp_vl (TD : ldltyO Σ) : oltyO Σ 0 := olty0 (λI ρ v,
    match ldlty_label TD with
    | None => ⊥
    | Some l => ∃ d, ⌜v @ l ↘ d⌝ ∧ TD ρ d
    end).
  Global Instance Proper_lift_dinterp_vl : Proper ((≡) ==> (≡)) lift_dinterp_vl.
  Proof.
    rewrite /lift_dinterp_vl => ??[/=??]; repeat case_match;
      simplify_eq; solve_proper_ho_equiv.
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

  Reserved Notation "A⟦ T ⟧".
  (* Observe the naming pattern for semantic type constructors:
  replace T by o. *)
  Fixpoint all_interp T : ldslty Σ :=
    let _ := (λ T, ldslty_olty (all_interp T)) : PTyInterp ty Σ in
    match T with
    | TTMem l L U => ldlty2ldslty $ oLDTMem l V⟦ L ⟧ V⟦ U ⟧
    | TVMem l T' => ldlty2ldslty $ oLDVMem l V⟦ T' ⟧

    | TAnd T1 T2 => LDsAnd A⟦T1⟧ A⟦T2⟧

    | TTop => LDsTop
    | TBot => olty2ldslty oBot

    | TOr T1 T2 => olty2ldslty $ oOr V⟦ T1 ⟧ V⟦ T2 ⟧
    | TLater T => olty2ldslty $ oLater V⟦ T ⟧
    | TPrim b => olty2ldslty $ oPrim b
    | TAll T1 T2 => olty2ldslty $ oAll V⟦ T1 ⟧ V⟦ T2 ⟧
    | TMu T => olty2ldslty $ oMu V⟦ T ⟧
    | TSel p l => olty2ldslty $ oSel p l
    | TSing p => olty2ldslty $ oSing p
    end
  where "A⟦ T ⟧" := (all_interp T).

  Global Instance pinterp : PTyInterp ty Σ :=
    λ T, ldslty_olty (all_interp T).
  Global Arguments pinterp _ /.
  Global Instance pinterp_lemmas: PTyInterpLemmas ty Σ.
  Proof.
    split; rewrite /pty_interpO /=.
    induction T => args sb1 sb2 w; rewrite /= /pty_interpO;
      properness; rewrite ?scons_up_swap ?hsubst_comp; trivial.
      by f_equiv => ?.
  Qed.

  Notation "LD⟦ T ⟧" := (ldslty_dlty A⟦ T ⟧).

  Definition def_interp T l ρ d := lift_ldlty LD⟦ T ⟧ ρ l d.
  Notation "D[ l ]⟦ T ⟧" := (def_interp T l).
  Notation "Ds⟦ T ⟧" := (all_interp T).

  Lemma ld_label_match T : ldlty_label LD⟦ T ⟧ = label_of_ty T.
  Proof. by destruct T. Qed.

  Definition idtp  Γ T l d     := sdtp l d  V⟦Γ⟧* LD⟦T⟧.
  Definition idstp Γ T ds      := sdstp ds  V⟦Γ⟧* Ds⟦T⟧.
  Definition ietp  Γ T e       := setp e    V⟦Γ⟧* V⟦T⟧.
  Definition istpi Γ T1 T2 i j := sstpi i j V⟦Γ⟧* V⟦T1⟧ V⟦T2⟧.
  Definition iptp  Γ T p i     := sptp p i  V⟦Γ⟧* V⟦T⟧.
  (* Global Arguments idstp /. *)

  (* Avoid auto-dropping box (and unfolding) when introducing judgments persistently. *)
  Local Notation IntoPersistent' P := (IntoPersistent false P P).

  Global Instance idtp_persistent Γ T l d: IntoPersistent' (idtp Γ T l d) | 0 := _.
  Global Instance idstp_persistent Γ T ds: IntoPersistent' (idstp Γ T ds) | 0 := _.
  Global Instance ietp_persistent Γ T e : IntoPersistent' (ietp Γ T e) | 0 := _.
  Global Instance istpi_persistent Γ T1 T2 i j : IntoPersistent' (istpi Γ T1 T2 i j) | 0 := _.
  Global Instance iptp_persistent Γ T p i : IntoPersistent' (iptp Γ T p i) | 0 := _.

  Implicit Types (T : olty Σ 0) (Td : ldlty Σ) (Tds : dslty Σ).

  Global Instance sdtp_persistent : IntoPersistent' (sdtp l d   Γ Td) | 0 := _.
  Global Instance sdstp_persistent : IntoPersistent' (sdstp ds  Γ Tds) | 0 := _.
  Global Instance setp_persistent : IntoPersistent' (setp e     Γ T) | 0 := _.
  Global Instance sstpi_persistent : IntoPersistent' (sstpi i j Γ T1 T2) | 0 := _.
  Global Instance sptp_persistent : IntoPersistent' (sptp p i   Γ T) | 0 := _.


  (* Backward compatibility. *)
  Definition oTMem l τ1 τ2 := ldslty_olty (ldlty2ldslty (oLDTMem l τ1 τ2)).
  Global Instance Proper_oTMem l : Proper ((≡) ==> (≡) ==> (≡)) (oTMem l).
  Proof. rewrite /oTMem/= => ??? ???. f_equiv. solve_proper. Qed.
  Definition oVMem l τ := ldslty_olty (ldlty2ldslty (oLDVMem l τ)).
  Global Instance Proper_oVMem l : Proper ((≡) ==> (≡)) (oVMem l).
  Proof. rewrite /oVMem/= => ???; f_equiv. solve_proper. Qed.
End SemTypes.

Global Instance: Params (@oAll) 2 := {}.

Section ldslty_defs.
  Context `{dlangG Σ}.
End ldslty_defs.

Notation "A⟦ T ⟧" := (all_interp T).
Notation "LD⟦ T ⟧" := (ldslty_dlty A⟦ T ⟧).
Notation "D[ l ]⟦ T ⟧" := (def_interp T l).
Notation "Ds⟦ T ⟧" := (ldslty_car A⟦ T ⟧).

(* Backward compatibility. *)
Notation "D*⟦ T ⟧" := (ldlty_car LD⟦ T ⟧).

Notation "d ↗ ψ" := (dm_to_type 0 d ψ) (at level 20).
Notation "G⟦ Γ ⟧" := s⟦ V⟦ Γ ⟧* ⟧*.

(** Single-definition typing *)
Notation "Γ ⊨ {  l := d  } : T" := (idtp Γ T l d) (at level 74, d, l, T at next level).
(** Multi-definition typing *)
Notation "Γ ⊨ds ds : T" := (idstp Γ T ds) (at level 74, ds, T at next level).
(** Expression typing *)
Notation "Γ ⊨ e : T" := (ietp Γ T e) (at level 74, e, T at next level).
Notation "Γ ⊨p p : T , i" := (iptp Γ T p i) (at level 74, p, T, i at next level).
Notation "Γ ⊨ T1 , i <: T2 , j " := (istpi Γ T1 T2 i j) (at level 74, T1, T2, i, j at next level).

Import stamp_transfer.
(** Judgment variants indexed by [gφ]. *)
Notation "Γ ⊨[ gφ  ] { l := d  } : T" := (wellMappedφ gφ → idtp Γ T l d)%I (at level 74, d, l, T at next level).
Notation "Γ ⊨ds[ gφ  ] ds : T" := (wellMappedφ gφ → idstp Γ T ds)%I (at level 74, ds, T at next level).
Notation "Γ ⊨[ gφ  ] e : T" := (wellMappedφ gφ → ietp Γ T e)%I (at level 74, e, T at next level).
Notation "Γ ⊨p[ gφ  ] p : T , i" := (wellMappedφ gφ → iptp Γ T p i)%I (at level 74, p, T, i at next level).
Notation "Γ ⊨[ gφ  ] T1 , i <: T2 , j" := (wellMappedφ gφ → istpi Γ T1 T2 i j)%I (at level 74, T1, T2, i, j at next level).

Section MiscLemmas.
  Context `{HdotG: dlangG Σ}.
  Implicit Types (τ L T U : olty Σ 0).

  Lemma def_interp_tvmem_eq l T p ρ :
    lift_ldlty (oLDVMem l T) ρ l (dpt p) ⊣⊢
    path_wp p (oClose T ρ).
  Proof.
    rewrite /lift_ldlty/=; iSplit. by iDestruct 1 as (_ pmem [= ->]) "$".
    iIntros "H"; iSplit; first done; iExists p. by auto.
  Qed.

  Context {Γ : sCtx Σ}.

  Lemma sSub_Refl T i : Γ s⊨ T, i <: T, i.
  Proof. by iIntros "!> **". Qed.

  Lemma sSub_Trans {T1 T2 T3 i1 i2 i3} : Γ s⊨ T1, i1 <: T2, i2 -∗
                                      Γ s⊨ T2, i2 <: T3, i3 -∗
                                      Γ s⊨ T1, i1 <: T3, i3.
  Proof.
    iIntros "#Hsub1 #Hsub2 !> * #Hg #HT".
    iApply ("Hsub2" with "[//] (Hsub1 [//] [//])").
  Qed.

  Lemma iterate_oLater_later {i} (τ : oltyO Σ i) n args ρ v:
    iterate oLater n τ args ρ v ⊣⊢ ▷^n τ args ρ v.
  Proof. elim: n => [//|n IHn]. by rewrite iterate_S /= IHn. Qed.

  Lemma sSub_Eq T U i j :
    Γ s⊨ T, i <: U, j ⊣⊢
    Γ s⊨ iterate oLater i T, 0 <: iterate oLater j U, 0.
  Proof. cbn. by setoid_rewrite iterate_oLater_later. Qed.

  Lemma pty_interp_subst (T : ty) σ : V⟦ T.|[σ] ⟧ ≡ V⟦ T ⟧.|[σ].
  Proof. intros ???; apply interp_subst_compose_ind. Qed.

  (* Lemma swap0 T σ args ρ v : V⟦ T.|[σ] ⟧ args ρ v ≡ (V⟦ T ⟧).|[σ] args ρ v.
  Proof. apply interp_subst_compose_ind. Qed. *)

  Lemma lift_olty_eq {i} {τ1 τ2 : oltyO Σ i} {args ρ v} :
    τ1 ≡ τ2 → τ1 args ρ v ≡ τ2 args ρ v.
  Proof. apply. Qed.
End MiscLemmas.

(** * Proper instances. *)
Section Propers.
  (** This instance doesn't allow setoid rewriting in the function argument
  to [iterate]. That's appropriate for this project. *)
  Global Instance: Params (@iterate) 3 := {}.
  Global Instance Proper_iterate {n} {A : ofeT} (f : A -> A) :
    Proper (equiv ==> equiv) f →
    Proper (equiv ==> equiv) (iterate f n).
  Proof.
    elim: n => [|n IHn] Hp x y Heq; rewrite ?(iterate_0, iterate_S) //.
    f_equiv. exact: IHn.
  Qed.

  Context `{HdotG: dlangG Σ}.

  Global Instance Proper_env_oltyped : Proper ((≡) ==> (=) ==> (≡)) env_oltyped.
  Proof.
    move => + + /equiv_Forall2 + + _ <-.
    elim => [|T1 G1 IHG1] [|T2 G2] /=; [done|inversion 1..|] =>
      /(Forall2_cons_inv _ _ _ _) [HT HG] ρ; f_equiv; [apply IHG1, HG|apply HT].
  Qed.
  Global Instance: Params (@env_oltyped) 2 := {}.

  (** ** Judgments *)
  Global Instance Proper_sstpi i j : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (sstpi i j).
  Proof.
    solve_proper_ho_equiv.
    (* intros ?? HG ?? H1 ?? H2; simplify_eq/=.
    properness; [by rewrite HG|apply H1|apply H2]. *)
  Qed.
  Global Instance Proper_sstpi_flip i j :
    Proper ((≡) --> (≡) --> (≡) --> flip (≡)) (sstpi i j).
  Proof. apply: flip_proper_4. Qed.
  Global Instance: Params (@sstpi) 4 := {}.


  Global Instance Proper_setp e : Proper ((≡) ==> (≡) ==> (≡)) (setp e).
  Proof.
    solve_proper_ho_equiv.
    (* intros ?? HG ?? HT ???; simplify_eq/=. by properness; [rewrite HG|apply HT]. *)
  Qed.
  Global Instance Proper_setp_flip e :
    Proper (flip (≡) ==> flip (≡) ==> flip (≡)) (setp e).
  Proof. apply: flip_proper_3. Qed.
  Global Instance: Params (@setp) 3 := {}.

  Global Instance Proper_sdtp l d : Proper ((≡) ==> (≡) ==> (≡)) (sdtp l d).
  Proof.
    move => ??? [??] [??] [??] /=; case_match; simplify_eq/=; properness => //;
      solve_proper_ho_equiv.
  Qed.
  Global Instance Proper_sdtp_flip l d : Proper (flip (≡) ==> flip (≡) ==> flip (≡)) (sdtp l d).
  Proof. apply: flip_proper_3. Qed.
  Global Instance: Params (@sdtp) 4 := {}.
End Propers.

Section defs.
  Context `{HdotG: dlangG Σ}.

  Lemma iterate_TLater_oLater i T:
    V⟦iterate TLater i T⟧ ≡ iterate oLater i V⟦T⟧.
  Proof. elim: i => [//|i IHi] ???. by rewrite !iterate_S /= (IHi _ _ _). Qed.

  Lemma iterate_TLater_later T n args ρ v:
    V⟦ iterate TLater n T ⟧ args ρ v ≡ (▷^n V⟦ T ⟧ args ρ v)%I.
  Proof.
    by rewrite (iterate_TLater_oLater n T _ _ _) iterate_oLater_later.
  Qed.

  Context {Γ : ctx}.

  Lemma Sub_Refl T i : Γ ⊨ T, i <: T, i.
  Proof. apply sSub_Refl. Qed.

  Lemma Sub_Trans {T1 T2 T3 i1 i2 i3} :
    Γ ⊨ T1, i1 <: T2, i2 -∗ Γ ⊨ T2, i2 <: T3, i3 -∗
    Γ ⊨ T1, i1 <: T3, i3.
  Proof. apply sSub_Trans. Qed.

  Lemma Sub_Eq T U i j :
    Γ ⊨ T, i <: U, j ⊣⊢
    Γ ⊨ iterate TLater i T, 0 <: iterate TLater j U, 0.
  Proof. by rewrite /istpi sSub_Eq !iterate_TLater_oLater. Qed.
End defs.

Import dlang_adequacy adequacy.
Theorem s_adequacy_dot_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} {e Ψ}
  (τ : ∀ `{dlangG Σ}, olty Σ 0)
  (Himpl : ∀ (Hdlang: dlangG Σ) v, oClose τ ids v -∗ ⌜Ψ v⌝)
  (Hlog : ∀ `{dlangG Σ} `(!SwapPropI Σ), allGs ∅ ==∗ [] s⊨ e : τ):
  ∀ σ, adequate NotStuck e σ (λ v _, Ψ v).
Proof.
  eapply (adequacy_dlang _); [apply Himpl | iIntros (??) "Hgs"].
  iMod (Hlog with "Hgs") as "#Htyp".
  iEval rewrite -(hsubst_id e). iApply ("Htyp" $! ids with "[//]").
Qed.

Theorem adequacy_dot_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} {e Ψ T}
  (Himpl : ∀ (Hdlang: dlangG Σ) v, V⟦ T ⟧ vnil ids v -∗ ⌜Ψ v⌝)
  (Hlog : ∀ `{dlangG Σ} `(!SwapPropI Σ), allGs ∅ ==∗ [] ⊨ e : T):
  ∀ σ, adequate NotStuck e σ (λ v _, Ψ v).
Proof. exact: (s_adequacy_dot_sem Σ (λ _, V⟦T⟧)). Qed.

Corollary s_safety_dot_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} {e}
  (τ : ∀ `{dlangG Σ}, olty Σ 0)
  (Hwp : ∀ `{dlangG Σ} `(!SwapPropI Σ), allGs ∅ ==∗ [] s⊨ e : τ):
  safe e.
Proof. apply adequate_safe, (s_adequacy_dot_sem Σ τ), Hwp; naive_solver. Qed.

Corollary safety_dot_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} {e T}
  (Hwp : ∀ `{dlangG Σ} `(!SwapPropI Σ), allGs ∅ ==∗ [] ⊨ e : T):
  safe e.
Proof. exact: (s_safety_dot_sem Σ (λ _, V⟦T⟧)). Qed.

(** Backward compatibility. *)
Definition ty_interp `{!dlangG Σ} T : envD Σ := pty_interpO T vnil.
Notation "⟦ T ⟧" := (ty_interp T).
Arguments ty_interp {_ _} _ /.
