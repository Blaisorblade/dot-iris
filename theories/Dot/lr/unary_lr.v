(** * Logical relation and semantic judgments. *)
From D Require Export iris_prelude proper lty lr_syn_aux.
From D Require Import iris_extra.det_reduction.
From D Require Import swap_later_impl.
From D.Dot Require Import syn path_repl.
From D.Dot Require Export dlang_inst path_wp.
From D.pure_program_logic Require Import weakestpre.

From D.Dot Require Export dot_lty.

Unset Program Cases.
Set Suggest Proof Using.
Set Default Proof Using "Type*".

Implicit Types (Σ : gFunctors)
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : env) (l : label).

(** The logical relation on values is [V⟦T⟧]. We also define the logical
    relation on definitions [Ds⟦T⟧].

    Both definitions follow the one on paper; concretely, they are defined
    through [C⟦T⟧] in instance [dot_interp].

    Binding and closing substitutions:

    Both relations interprets *open* types into predicates over values that
    are meant to be closed. So for instance [V⟦T⟧ T args ρ v] applies substitution [ρ]
    to [T], but not to [v]. We don't actually require that [v] be closed.

    Semantic judgements must apply instead to open subjects (terms/value/paths),
    so they apply substitutions to their subject.

    Additionally, both apply to *stamped* syntax, hence they only expect
    [dtysem] and not [dtysyn] for type member definitions.
 *)

(** ** Define fully semantic judgments. They accept arbitrary semantic types. *)

Section judgments.
  Context {Σ}.
  Implicit Types (τ : oltyO Σ 0).

  (** Expression typing *)
  Definition setp `{!dlangG Σ} e Γ τ : iProp Σ :=
    |==> ∀ ρ, sG⟦Γ⟧* ρ → ◇ sE⟦ τ ⟧ ρ (e.|[ρ]).
  Global Arguments setp : simpl never.

  (** Delayed subtyping. *)
  Definition sstpd `{!dlangG Σ} i Γ τ1 τ2 : iProp Σ :=
    |==> ∀ ρ,
      sG⟦Γ⟧*ρ → ◇ ▷^i (oClose τ1 ρ ⊆ oClose τ2 ρ).
  Global Arguments sstpd : simpl never.

  (** Multi-definition typing *)
  Definition sdstp `{!dlangG Σ} ds Γ (T : clty Σ) : iProp Σ :=
    |==> ⌜wf_ds ds⌝ ∧ ∀ ρ, ⌜path_includes (pv (ids 0)) ρ ds ⌝ → sG⟦Γ⟧* ρ → ◇ T ρ ds.|[ρ].
  Global Arguments sdstp : simpl never.

  (** Definition typing *)
  Definition sdtp `{!dlangG Σ} l d Γ (φ : clty Σ): iProp Σ := sdstp [(l, d)] Γ φ.
  Global Arguments sdtp : simpl never.

  (** Path typing *)
  Definition sptp `{!dlangG Σ} p i Γ (T : oltyO Σ 0): iProp Σ :=
    |==> ∀ ρ, sG⟦Γ⟧* ρ →
      ◇ ▷^i path_wp p.|[ρ] (oClose T ρ).
  Global Arguments sptp : simpl never.
End judgments.

(** Expression typing *)
Notation "Γ s⊨ e : τ" := (setp e Γ τ) (at level 74, e, τ at next level).
(** Delayed subtyping. *)
Notation "Γ s⊨ T1 <:[ i  ] T2" := (sstpd i Γ T1 T2) (at level 74, T1, T2 at next level).
(** Single-definition typing *)
Notation "Γ s⊨ {  l := d  } : T" := (sdtp l d Γ T) (at level 64, d, l, T at next level).
(** Multi-definition typing *)
Notation "Γ s⊨ds ds : T" := (sdstp ds Γ T) (at level 74, ds, T at next level).
(** Path typing *)
Notation "Γ s⊨p p : τ , i" := (sptp p i Γ τ) (at level 74, p, τ, i at next level).

Section JudgEqs.
  Context `{HdotG: !dlangG Σ}.

  Lemma sstpd_eq_1 Γ T1 i T2 :
    Γ s⊨ T1 <:[i] T2 ⊣⊢
    |==> ∀ ρ, sG⟦Γ⟧* ρ → ∀ v, ◇ ▷^i (T1 vnil ρ v → T2 vnil ρ v).
  Proof.
    rewrite /sstpd /subtype_lty; f_equiv; f_equiv => ρ.
    by rewrite laterN_forall except_0_forall.
  Qed.

  Lemma sstpd_eq Γ T1 i T2 :
    Γ s⊨ T1 <:[i] T2 ⊣⊢
    |==> ∀ ρ v, sG⟦Γ⟧* ρ → ◇ ▷^i (T1 vnil ρ v → T2 vnil ρ v).
  Proof. rewrite sstpd_eq_1; properness. apply: forall_swap_impl. Qed.
End JudgEqs.

(** When a definition points to a semantic type. Inlined in paper. *)
Definition dm_to_type `{HdotG: !dlangG Σ} d i (ψ : hoD Σ i) : iProp Σ :=
  ∃ s σ, ⌜ d = dtysem σ s ⌝ ∧ s ↗n[ σ , i ] ψ.
Notation "d ↗n[ i  ] ψ" := (dm_to_type d i ψ) (at level 20).

Section dm_to_type.
  Context `{HdotG: !dlangG Σ}.

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

  Global Opaque dm_to_type.
End dm_to_type.

(** ** Semantic path substitution and replacement. *)

(** Semantic substitution of path in type. *)
Definition opSubst `{!dlangG Σ} {n} p (T : oltyO Σ n) : oltyO Σ n :=
  Olty (λI args ρ v, path_wp p.|[ρ] (λ w, T args (w .: ρ) v)).
Notation "T .sTp[ p /]" := (opSubst p T) (at level 65).

(** Semantic definition of path replacement. *)
Definition sem_ty_path_replI {Σ n} p q (T1 T2 : olty Σ n) : iProp Σ :=
  |==> ∀ args ρ v (H : alias_paths p.|[ρ] q.|[ρ]), T1 args ρ v ≡ T2 args ρ v.
Notation "T1 ~sTpI[ p := q  ]* T2" :=
  (sem_ty_path_replI p q T1 T2) (at level 70).

(** Semantic definition of path replacement: alternative, weaker version.
Unlike [sem_ty_path_replI], this version in [Prop] is less expressive, but
sufficient for our goals and faster to use in certain proofs. *)
Definition sem_ty_path_repl {Σ n} p q (T1 T2 : olty Σ n) : Prop :=
  ∀ args ρ v, alias_paths p.|[ρ] q.|[ρ] → T1 args ρ v ≡ T2 args ρ v.
Notation "T1 ~sTpP[ p := q  ]* T2" :=
  (sem_ty_path_repl p q T1 T2) (at level 70).

Section path_repl.
  Context `{!dlangG Σ}.

  Lemma opSubst_pv_eq {n} v (T : oltyO Σ n) : T .sTp[ pv v /] ≡ T.|[v/].
  Proof. move=> args ρ w /=. by rewrite path_wp_pv_eq subst_swap_base. Qed.

  Lemma sem_psubst_one_repl {n} {T : olty Σ n} {args p v w ρ}:
    alias_paths p.|[ρ] (pv v) →
    T .sTp[ p /] args ρ w ≡ T args (v .: ρ) w.
  Proof. move=> /alias_paths_elim_eq /= ->. by rewrite path_wp_pv_eq. Qed.

  Lemma sem_ty_path_repl_eq {n} {p q} {T1 T2 : olty Σ n} :
    T1 ~sTpP[ p := q ]* T2 → ⊢ T1 ~sTpI[ p := q ]* T2.
  Proof. iIntros "%Heq !% /=". apply: Heq. Qed.
  (* The reverse does not hold. *)
End path_repl.

(** ** gDOT semantic types. *)
Definition vl_sel `{!dlangG Σ} {n} vp l args v : iProp Σ :=
  ∃ d ψ, ⌜vp @ l ↘ d⌝ ∧ d ↗n[ n ] ψ ∧ packHoLtyO ψ args v.

Definition oSelN `{!dlangG Σ} n p l : oltyO Σ n :=
  Olty (λI args ρ v, path_wp p.|[ρ] (λ vp, vl_sel vp l args v)).
Notation oSel := (oSelN 0).

Section sem_types.
  Context `{HdotG: !dlangG Σ}.

  Definition oDTMemRaw n (rK : env → hoD Σ n → iProp Σ): dltyO Σ := Dlty (λI ρ d,
    ∃ ψ, d ↗n[ n ] ψ ∧ rK ρ ψ).

  Implicit Types (τ : oltyO Σ 0).

  (** Not a "real" kind, just a predicate over types. *)
  Definition dot_intv_type_pred τ1 τ2 ρ ψ : iProp Σ :=
    τ1 vnil ρ ⊆ packHoLtyO ψ vnil ∧ packHoLtyO ψ vnil ⊆ τ2 vnil ρ.

  (** [ D⟦ { A :: τ1 .. τ2 } ⟧ ]. *)
  Definition oDTMem τ1 τ2 : dltyO Σ := oDTMemRaw _ (dot_intv_type_pred τ1 τ2).
  Global Instance oDTMem_proper : Proper ((≡) ==> (≡) ==> (≡)) oDTMem.
  Proof.
    rewrite /oDTMem => ??? ??? ??/=; properness; try reflexivity;
      solve_proper_ho.
  Qed.

  (** [ D⟦ { a : τ } ⟧ ]. *)
  Definition oDVMem τ : dltyO Σ := Dlty (λI ρ d,
    ∃ pmem, ⌜d = dpt pmem⌝ ∧ path_wp pmem (oClose τ ρ)).
  Global Instance oDVMem_proper : Proper ((≡) ==> (≡)) oDVMem.
  Proof.
    rewrite /oDVMem => ??? ??/=; properness; try reflexivity;
      apply path_wp_proper => ?; hof_eq_app.
  Qed.

  Lemma oDVMem_eq T ρ p :
    oDVMem T ρ (dpt p) ≡ path_wp p (oClose T ρ).
  Proof. simpl; iSplit; last by eauto. by iDestruct 1 as (pmem [= ->]) "$". Qed.

  (** Lift [oDTMem] and [oDVMem] to full [clty]s, [cTMem] and [cVMem]. *)

  (** [ Ds⟦ { l :: τ1 .. τ2 } ⟧] and [ V⟦ { l :: τ1 .. τ2 } ⟧ ]. *)
  Definition cTMem l τ1 τ2 : clty Σ := dty2clty l (oDTMem τ1 τ2).
  Global Instance cTMem_proper l : Proper ((≡) ==> (≡) ==> (≡)) (cTMem l).
  Proof. solve_proper. Qed.

  Lemma cTMem_eq l T1 T2 d ρ :
    cTMem l T1 T2 ρ [(l, d)] ⊣⊢ oDTMem T1 T2 ρ d.
  Proof. apply dty2clty_singleton. Qed.

  (** [ Ds⟦ { l : τ } ⟧] and [ V⟦ { l : τ } ⟧ ]. *)
  Definition cVMem l τ : clty Σ := dty2clty l (oDVMem τ).
  Global Instance cVMem_proper l : Proper ((≡) ==> (≡)) (cVMem l).
  Proof. solve_proper. Qed.

  Lemma cVMem_eq l T d ρ :
    cVMem l T ρ [(l, d)] ⊣⊢ oDVMem T ρ d.
  Proof. apply dty2clty_singleton. Qed.

  Lemma oSel_pv {n} w l args ρ v :
    oSelN n (pv w) l args ρ v ⊣⊢
      ∃ d ψ, ⌜w.[ρ] @ l ↘ d⌝ ∧ d ↗n[ n ] ψ ∧ ▷ ψ args v.
  Proof. by rewrite /= path_wp_pv_eq. Qed.

  (** [ V⟦ p.type ⟧]. *)
  Definition oSing `{!dlangG Σ} p : olty Σ 0 := olty0 (λI ρ v, ⌜alias_paths p.|[ρ] (pv v)⌝).

  (** [ V⟦ ∀ x: τ1. τ2 ⟧]. *)
  (* Function types; this definition is contractive (similarly to what's
     useful for equi-recursive types). *)
  Definition oAll τ1 τ2 := olty0
    (λI ρ v,
    (∃ t, ⌜ v = vabs t ⌝ ∧
     ∀ w, ▷ τ1 vnil ρ w → ▷ sE⟦ τ2 ⟧ (w .: ρ) t.|[w/])).

  Global Instance oAll_proper : Proper ((≡) ==> (≡) ==> (≡)) oAll.
  Proof. solve_proper_ho. Qed.

  (** Semantics of primitive types. *)
  Definition oPrim b : olty Σ 0 := olty0 (λI ρ v, ⌜pure_interp_prim b v⌝).

  (** Dispatch function defining [V⟦ T ⟧] and [Ds⟦ T ⟧]. *)
  (* Observe the naming pattern for semantic type constructors:
  replace T by o (for most constructors) or by c (for constructors producing
  cltys). *)
  Global Instance dot_interp : CTyInterp Σ := fix dot_interp T :=
    let _ := dot_interp : CTyInterp Σ in
    match T with
    | TTMem l L U => cTMem l V⟦ L ⟧ V⟦ U ⟧
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
    | TSel p l => olty2clty $ oSel p l
    | TSing p => olty2clty $ oSing p
    end.

  (** Unfolding lemma for [TAnd]: defined because [simpl] on the LHS produces
      [oAnd C⟦ T1 ⟧ C⟦ T2 ⟧]. *)
  Lemma interp_TAnd_eq T1 T2 : V⟦ TAnd T1 T2 ⟧ ≡ oAnd V⟦ T1 ⟧ V⟦ T2 ⟧.
  Proof. done. Qed.

  (** Binding lemmas for [V⟦ T ⟧] and [Ds⟦ T ⟧]. *)
  Global Instance pinterp_lemmas: CTyInterpLemmas Σ.
  Proof.
    split; rewrite /pty_interp;
      induction T => args sb1 sb2 w; rewrite /= /pty_interp /dot_intv_type_pred /subtype_lty /=;
      properness; rewrite ?scons_up_swap ?hsubst_comp; trivial.
    by apply path_wp_proper => ?.
  Qed.

  Definition idtp  Γ T l d     := sdtp l d  V⟦Γ⟧* C⟦T⟧.
  Definition idstp Γ T ds      := sdstp ds  V⟦Γ⟧* C⟦T⟧.
  Definition ietp  Γ T e       := setp e    V⟦Γ⟧* V⟦T⟧.
  Definition istpd i Γ T1 T2   := sstpd i   V⟦Γ⟧* V⟦T1⟧ V⟦T2⟧.
  Definition iptp  Γ T p i     := sptp p i  V⟦Γ⟧* V⟦T⟧.
End sem_types.

Global Instance: Params (@oAll) 2 := {}.

Notation "d ↗ ψ" := (dm_to_type 0 d ψ) (at level 20).
Notation "G⟦ Γ ⟧ ρ" := (sG⟦ V⟦ Γ ⟧* ⟧* ρ) (at level 10).

(** Single-definition typing *)
Notation "Γ ⊨ {  l := d  } : T" := (idtp Γ T l d) (at level 74, d, l, T at next level).
(** Multi-definition typing *)
Notation "Γ ⊨ds ds : T" := (idstp Γ T ds) (at level 74, ds, T at next level).
(** Expression typing *)
Notation "Γ ⊨ e : T" := (ietp Γ T e) (at level 74, e, T at next level).
Notation "Γ ⊨p p : T , i" := (iptp Γ T p i) (at level 74, p, T, i at next level).
Notation "Γ ⊨ T1 <:[ i  ] T2" := (istpd i Γ T1 T2) (at level 74, T1, T2 at next level).

Notation oInt := (oPrim tint).
Notation oBool := (oPrim tbool).

Notation oTMem l τ1 τ2 := (clty_olty (cTMem l τ1 τ2)).
Notation oVMem l τ := (clty_olty (cVMem l τ)).

(** ** Show these typing judgments are equivalent to what we present in the paper. *)
Section judgment_definitions.
  Context `{HdotG: !dlangG Σ}.

  Implicit Types (T : ty) (Γ : ctx).

  Lemma path_includes_equiv p ρ ds : path_includes (pv (ids 0)) ρ ds ↔
    ∃ ds', ρ 0 = vobj ds' ∧ ds.|[ρ] `sublist_of` selfSubst ds' ∧ wf_ds ds'.
  Proof. by rewrite /path_includes path_wp_pure_pv_eq. Qed.

  Lemma idstp_eq Γ T ds : Γ ⊨ds ds : T ⊣⊢
    |==> ⌜wf_ds ds⌝ ∧ ∀ ρ, ⌜path_includes (pv (ids 0)) ρ ds ⌝ → G⟦Γ⟧ ρ →
      ◇ Ds⟦T⟧ ρ ds.|[ρ].
  Proof. reflexivity. Qed.

  Lemma ietp_eq Γ e T :
    Γ ⊨ e : T ⊣⊢ |==> ∀ ρ, G⟦Γ⟧ ρ → ◇ E⟦T⟧ ρ (e.|[ρ]).
  Proof. reflexivity. Qed.

  Lemma istpd_eq Γ T1 i T2 :
    Γ ⊨ T1 <:[i] T2 ⊣⊢
    |==> ∀ ρ v, G⟦Γ⟧ ρ → ◇ ▷^i (V⟦T1⟧ vnil ρ v → V⟦T2⟧ vnil ρ v).
  Proof. apply sstpd_eq. Qed.

  Lemma iptp_eq Γ p T i :
    Γ ⊨p p : T , i ⊣⊢
    |==> ∀ ρ, G⟦Γ⟧ ρ →
      ◇ ▷^i path_wp (p.|[ρ]) (λ v, V⟦T⟧ vnil ρ v).
  Proof. reflexivity. Qed.
End judgment_definitions.

Section misc_lemmas.
  Context `{HdotG: !dlangG Σ}.
  Implicit Types (τ L T U : olty Σ 0).

  Lemma iterate_TLater_oLater i (T : ty) :
    V⟦iterate TLater i T⟧ ≡ oLaterN i V⟦T⟧.
  Proof. elim: i => [//|i IHi] ???; by rewrite !iterate_S /= IHi. Qed.

  Lemma oVMem_eq l T vnil ρ v :
    oVMem l T vnil ρ v ⊣⊢
    ∃ pmem, ⌜v @ l ↘ dpt pmem⌝ ∧ path_wp pmem (oClose T ρ).
  Proof.
    etrans; [apply bi_exist_nested_swap|]; apply bi.exist_proper => p.
    rewrite and2_exist_r.
    apply bi.and_proper, reflexivity; iIntros "!% /="; naive_solver.
  Qed.

  Lemma oTMem_eq l τ1 τ2 args ρ v :
    oTMem l τ1 τ2 args ρ v ⊣⊢
    ∃ ψ d, ⌜v @ l ↘ d⌝ ∧ d ↗n[ 0 ] ψ ∧ dot_intv_type_pred τ1 τ2 ρ ψ.
  Proof. apply bi_exist_nested_swap. Qed.

  Lemma oTMem_shift A L U : oTMem A (shift L) (shift U) = shift (oTMem A L U).
  Proof. done. Qed.

  (** Core lemmas about type selections and bounds. *)
  Lemma vl_sel_ub w l L U ρ v :
    vl_sel w l vnil v -∗
    oTMem l L U vnil ρ w -∗
    U vnil ρ v.
  Proof.
    iIntros "Hφ"; iDestruct 1 as (d1 Hl1 φ1) "(Hdφ1 & _ & HφU)".
    iApply "HφU".
    iDestruct "Hφ" as (d2 φ2 Hl2) "[Hdφ2 Hφ2v]".
    objLookupDet; iDestruct (dm_to_type_agree vnil v with "Hdφ2 Hdφ1") as "Hag".
    iNext. by iRewrite "Hag" in "Hφ2v".
  Qed.

  Lemma vl_sel_lb w l L U ρ v :
    L vnil ρ v -∗
    oTMem l L U vnil ρ w -∗
    vl_sel w l vnil v.
  Proof.
    iIntros "HL"; iDestruct 1 as (d Hl φ) "[Hdφ [HLφ _]]".
    iExists d, φ; iFrame (Hl) "Hdφ". iApply ("HLφ" with "HL").
  Qed.

  Lemma lift_sub_dty2cltyN i (T1 T2 : dlty Σ) l ρ :
    (∀ d, ▷^i T1 ρ d -∗ ▷^i T2 ρ d) ⊢
    oLaterN i (lift_dty_vl l T1) vnil ρ ⊆ oLaterN i ((lift_dty_vl l T2)) vnil ρ.
  Proof.
    iIntros "Hsub %v". iDestruct 1 as (d) "[Hl #H1]"; iExists d; iFrame "Hl".
    by iApply ("Hsub" with "H1").
  Qed.

  Lemma lift_sub_dty2clty (T1 T2 : dlty Σ) l ρ :
    (∀ d, T1 ρ d -∗ T2 ρ d) ⊢
    lift_dty_vl l T1 vnil ρ ⊆ lift_dty_vl l T2 vnil ρ.
  Proof. apply (lift_sub_dty2cltyN 0). Qed.

  Lemma oDTMem_respects_sub L1 L2 U1 U2 ρ d :
    L2 vnil ρ ⊆ L1 vnil ρ -∗
    U1 vnil ρ ⊆ U2 vnil ρ -∗
    oDTMem L1 U1 ρ d -∗ oDTMem L2 U2 ρ d.
  Proof.
    iIntros "#HsubL #HsubU"; iDestruct 1 as (φ) "#(Hφl & #HLφ & #HφU)".
    iExists φ; iSplit; first done; iSplit; iIntros "%w #Hw".
    - iApply ("HLφ" with "(HsubL Hw)").
    - iApply ("HsubU" with "(HφU Hw)").
  Qed.

  Lemma oTMem_respects_sub L1 L2 U1 U2 ρ l :
    L2 vnil ρ ⊆ L1 vnil ρ -∗
    U1 vnil ρ ⊆ U2 vnil ρ -∗
    oTMem l L1 U1 vnil ρ ⊆ oTMem l L2 U2 vnil ρ.
  Proof.
    rewrite -lift_sub_dty2clty; iIntros "#HsubL #HsubU %d".
    iApply (oDTMem_respects_sub with "HsubL HsubU").
  Qed.

  Lemma oDVMem_respects_subN i T1 T2 ρ d :
    oClose (oLaterN i T1) ρ ⊆ oClose (oLaterN i T2) ρ ⊢
    ▷^i oDVMem T1 ρ d -∗ ▷^i oDVMem T2 ρ d.
  Proof.
    iIntros "Hsub"; iDestruct 1 as (pmem) "[Heq HT1]"; iExists pmem; iFrame "Heq".
    iApply (path_wp_wand_laterN with "HT1"); iIntros "%v HT1".
    by iApply ("Hsub" with "HT1").
  Qed.
  Definition oDVMem_respects_sub := oDVMem_respects_subN 0.

  Lemma oVMem_respects_subN i T1 T2 l ρ :
    oClose (oLaterN i T1) ρ ⊆ oClose (oLaterN i T2) ρ ⊢
    oLaterN i (oVMem l T1) vnil ρ ⊆ oLaterN i (oVMem l T2) vnil ρ.
  Proof.
    rewrite -lift_sub_dty2cltyN. iIntros "Hsub %d".
    iApply (oDVMem_respects_subN with "Hsub").
  Qed.
  Definition oVMem_respects_sub := oVMem_respects_subN 0.

  Lemma sdtp_eq (Γ : sCtx Σ) (T : clty Σ) l d:
    Γ s⊨ { l := d } : T ⊣⊢
      |==> ∀ ρ, ⌜path_includes (pv (ids 0)) ρ [(l, d)]⌝ → sG⟦Γ⟧* ρ → ◇ T ρ [(l, d.|[ρ])].
  Proof.
    rewrite /sdtp /sdstp pure_True ?(left_id _ bi_and);
      by [> | exact: NoDup_singleton].
  Qed.

  Lemma sdtp_eq' (Γ : sCtx Σ) (T : dlty Σ) l d:
    Γ s⊨ { l := d } : dty2clty l T ⊣⊢
      |==> ∀ ρ, ⌜path_includes (pv (ids 0)) ρ [(l, d)]⌝ → sG⟦Γ⟧* ρ → ◇ T ρ d.|[ρ].
  Proof. by rewrite sdtp_eq; properness; last (f_equiv; apply dty2clty_singleton). Qed.

  Lemma ipwp_terminates {p T i}:
    [] s⊨p p : T , i ⊢ ◇ ▷^i ⌜ terminates (path2tm p) ⌝.
  Proof.
    iIntros ">#H".
    iMod ("H" $! ids with "[//]") as "{H}H"; rewrite hsubst_id.
    iApply (path_wp_terminates with "H").
  Qed.

  (** This typing lemma is here to be usable in proof of other lemmas. *)
  Lemma sT_Path {Γ τ p} :
    Γ s⊨p p : τ, 0 -∗ Γ s⊨ path2tm p : τ.
  Proof.
    iIntros ">#Hep !> %ρ #Hg /="; rewrite path2tm_subst -path_wp_to_wp.
    iApply ("Hep" with "Hg").
  Qed.
End misc_lemmas.

Section path_repl_lemmas.
  Context `{!dlangG Σ}.
  Implicit Types (φ : vl -d> iPropO Σ).

  (** Beware: we can do path replacement *before* substitution,
      even tho substitution and path replacement don't commute nicely.

      As a special case, we get the less surprising:
      [alias_paths_subst p r ids → path_wp q φ ≡ path_wp (q .p[p := r]) φ].

      But we do need the general form. *)
  Lemma path_replacement_equiv {p q ρ} p1 p2 φ :
    p1 ~pp[ p := q ] p2 →
    alias_paths p.|[ρ] q.|[ρ] →
    path_wp p1.|[ρ] φ ≡ path_wp p2.|[ρ] φ.
  Proof.
    move => Hrepl; elim: Hrepl φ => {p1 p2} [| p1' p2' l Hrepl IHrepl] φ /=.
    exact: alias_paths_elim_eq.
    rewrite !path_wp_pself_eq /= => Hal.
    properness => //. exact: IHrepl.
  Qed.

  Lemma rewrite_path_path_repl {p q p1 p2 ρ v}:
    p1 ~pp[ p := q ] p2 →
    alias_paths p.|[ρ] q.|[ρ] → (* p : q.type *)
    ⌜alias_paths p1.|[ρ] (pv v)⌝ ⊣⊢@{iPropI Σ} ⌜alias_paths p2.|[ρ] (pv v)⌝.
    (* alias_paths p1.|[ρ] (pv v) ↔ alias_paths p2.|[ρ] (pv v). *)
  Proof.
    intros Hrew Hal.
    rewrite !alias_paths_pv_eq_1 -!path_wp_pureable.
    exact: path_replacement_equiv.
  Qed.

  Lemma fundamental_ty_path_repl {p q T1 T2}
    (Hrew : T1 ~Tp[ p := q ] T2) :
    V⟦ T1 ⟧ ~sTpP[ p := q ]* V⟦ T2 ⟧.
  Proof.
    rewrite /sem_ty_path_repl; induction Hrew => args ρ v He /=;
      rewrite /dot_intv_type_pred /subtype_lty/=; properness;
      try by [ exact: path_replacement_equiv | exact: rewrite_path_path_repl
         | apply IHHrew; rewrite ?hsubst_comp | | f_equiv => ?; exact: IHHrew].
  Qed.

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

(** Proper instances. *)
Section Propers.
  (** This instance doesn't allow setoid rewriting in the function argument
  to [iterate]. That's appropriate for this project. *)
  Global Instance: Params (@iterate) 3 := {}.
  Global Instance iterate_proper {n} {A : ofeT} (f : A → A) :
    Proper (equiv ==> equiv) f →
    Proper (equiv ==> equiv) (iterate f n).
  Proof.
    elim: n => [|n IHn] Hp x y Heq; rewrite ?(iterate_0, iterate_S) //.
    f_equiv. exact: IHn.
  Qed.

  Context `{HdotG: !dlangG Σ}.

  (** Judgments *)
  Global Instance sstpd_proper i : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (sstpd i).
  Proof.
    solve_proper_ho.
    (* intros ?? HG ?? H1 ?? H2; rewrite /sstpd /subtype_lty;
    properness; [by rewrite HG|apply H1|apply H2]. *)
  Qed.
  Global Instance sstpd_flip_proper i :
    Proper ((≡) --> (≡) --> (≡) --> flip (≡)) (sstpd i).
  Proof. apply: flip_proper_4. Qed.
  Global Instance: Params (@sstpd) 3 := {}.


  Global Instance setp_proper e : Proper ((≡) ==> (≡) ==> (≡)) (setp e).
  Proof.
    solve_proper_ho.
    (* intros ?? HG ?? HT ???; simplify_eq/=. by properness; [rewrite HG|apply HT]. *)
  Qed.
  Global Instance setp_flip_proper e :
    Proper (flip (≡) ==> flip (≡) ==> flip (≡)) (setp e).
  Proof. apply: flip_proper_3. Qed.
  Global Instance: Params (@setp) 3 := {}.

  Global Instance sdstp_proper ds : Proper ((≡) ==> (≡) ==> (≡)) (sdstp ds).
  Proof.
    by rewrite /sdstp => ??? [?? _ _ _] [?? _ _ _] [/= ??]; properness; repeat f_equiv.
  Qed.
  Global Instance sdstp_flip_proper ds :
    Proper (flip (≡) ==> flip (≡) ==> flip (≡)) (sdstp ds).
  Proof. apply: flip_proper_3. Qed.
  Global Instance: Params (@sdstp) 3 := {}.

  Global Instance sdtp_proper l d : Proper ((≡) ==> (≡) ==> (≡)) (sdtp l d) := _.
  Global Instance sdtp_flip_proper l d : Proper (flip (≡) ==> flip (≡) ==> flip (≡)) (sdtp l d) := _.
  Global Instance: Params (@sdtp) 4 := {}.

  Global Instance sptp_proper p i : Proper ((≡) ==> (≡) ==> (≡)) (sptp p i).
  Proof. solve_proper_ho. Qed.
  Global Instance sptp_flip_proper p i : Proper ((≡) --> (≡) --> flip (≡)) (sptp p i).
  Proof. apply: flip_proper_3. Qed.
  Global Instance: Params (@sptp) 4 := {}.
End Propers.

(** Backward compatibility. *)
Notation "⟦ T ⟧" := (oClose V⟦ T ⟧).

Import dlang_adequacy.

(** Adequacy of normalization for gDOT paths. *)
Lemma ipwp_gs_adequacy Σ `{HdlangG : !dlangG Σ} `{!SwapPropI Σ} {p T i}
  (Hwp : ∀ `(Hdlang : !dlangG Σ) `(!SwapPropI Σ), ⊢ [] ⊨p p : T , i):
  terminates (path2tm p).
Proof.
  eapply (@soundness (iResUR Σ) _ (S i)).
  rewrite /= -except_0_later.
  apply (bupd_plain_soundness _).
  rewrite -later_intro.
  iApply ipwp_terminates.
  iApply Hwp.
Qed.
