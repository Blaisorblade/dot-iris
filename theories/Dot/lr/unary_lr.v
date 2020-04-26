From iris.proofmode Require Import tactics.
From D Require Export iris_prelude proper lty lr_syn_aux.
From D Require Import iris_extra.det_reduction.
From D Require Import swap_later_impl.
From D.Dot Require Import syn.
From D.Dot Require Export dlang_inst path_wp.
From D.pure_program_logic Require Import weakestpre.

From D.Dot Require Export dot_lty.

Unset Program Cases.
Set Suggest Proof Using.
Set Default Proof Using "Type*".

Implicit Types (Σ : gFunctors)
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (vs : vls) (ρ : var → vl) (l : label).

(** * Semantic domains. *)

(** The logical relation on values is [V⟦T⟧]. We also define the logical
    relation on definitions Ds⟦T⟧.

    Both definitions follow the one on paper; concretely, they are defined
    through C⟦T⟧ in instance [dot_interp].

    Binding and closing substitutions:

    Both relations interprets *open* types into predicates over values that
    are meant to be closed. So for instance [V⟦T⟧ T args ρ v] applies substitution [ρ]
    to [T], but not to [v]. We don't actually require that [v] be closed.

    Semantic judgements must apply instead to open subjects (terms/value/paths),
    so they apply substitutions to their subject.

    Additionally, both apply to *stamped* syntax, hence they only expect
    [dtysem] and not [dtysyn] for type member definitions.
 *)

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
  Definition setp `{!dlangG Σ} e Γ τ : iProp Σ :=
    □∀ ρ, s⟦Γ⟧* ρ → E⟦ τ ⟧ ρ (e.|[ρ]).
  Global Arguments setp /.

  (** Indexed subtyping. *)
  Definition sstpi `{!dlangG Σ} i j Γ τ1 τ2 : iProp Σ :=
    □∀ ρ v,
      s⟦Γ⟧*ρ → ▷^i oClose τ1 ρ v → ▷^j oClose τ2 ρ v.
  Global Arguments sstpi /.

  (** Multi-definition typing *)
  Definition sdstp `{!dlangG Σ} ds Γ (T : clty Σ) : iProp Σ :=
    ⌜wf_ds ds⌝ ∧ □∀ ρ, ⌜path_includes (pv (ids 0)) ρ ds ⌝ → s⟦Γ⟧* ρ → T ρ ds.|[ρ].
  Global Arguments sdstp /.

  (** Definition typing *)
  Definition sdtp `{!dlangG Σ} l d Γ (φ : clty Σ): iProp Σ := sdstp [(l, d)] Γ φ.
  Global Arguments sdtp /.

  (** Path typing *)
  Definition sptp `{!dlangG Σ} p i Γ (T : oltyO Σ 0): iProp Σ :=
    □∀ ρ, s⟦Γ⟧* ρ →
      ▷^i path_wp (p.|[ρ]) (oClose T ρ).
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

Definition dm_to_type `{HdotG: !dlangG Σ} d i (ψ : hoD Σ i) : iProp Σ :=
  ∃ s σ, ⌜ d = dtysem σ s ⌝ ∧ s ↗n[ σ , i ] ψ.
Notation "d ↗n[ i  ] ψ" := (dm_to_type d i ψ) (at level 20).

Section dm_to_type.
  Context `{HdotG: !dlangG Σ}.

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

Definition oSelN `{!dlangG Σ} n p l : oltyO Σ n :=
  Olty (λI args ρ v, path_wp p.|[ρ]
    (λ vp, ∃ ψ d, ⌜vp @ l ↘ d⌝ ∧ d ↗n[ n ] ψ ∧ ▷ □ ψ args v)).
Notation oSel := (oSelN 0).

Section SemTypes.
  Context `{HdotG: !dlangG Σ}.

  Implicit Types (τ : oltyO Σ 0).

  Definition oDTMem τ1 τ2 : dltyO Σ := Dlty (λI ρ d,
    ∃ ψ, d ↗n[ 0 ] ψ ∧
       □ ((∀ v, ▷ τ1 vnil ρ v → ▷ □ ψ vnil v) ∧
          (∀ v, ▷ □ ψ vnil v → ▷ τ2 vnil ρ v))).
  Global Instance Proper_oDTMem : Proper ((≡) ==> (≡) ==> (≡)) oDTMem.
  Proof.
    rewrite /oDTMem => ??? ??? ??/=; properness; try reflexivity; ho_f_equiv.
  Qed.

  Definition oDVMem τ : dltyO Σ := Dlty (λI ρ d,
    ∃ pmem, ⌜d = dpt pmem⌝ ∧ path_wp pmem (oClose τ ρ)).
  Global Instance Proper_oDVMem : Proper ((≡) ==> (≡)) oDVMem.
  Proof.
    rewrite /oDVMem => ??? ??/=; properness; try reflexivity;
      apply path_wp_proper => ?; ho_f_equiv.
  Qed.

  Lemma oDVMem_eq T ρ p :
    oDVMem T ρ (dpt p) ≡ path_wp p (oClose T ρ).
  Proof. simpl; iSplit; last by eauto. by iDestruct 1 as (pmem [= ->]) "$". Qed.

  (** [cTMem] and [cVMem] are full [clty]. *)
  Definition cTMem l τ1 τ2 : clty Σ := dty2clty l (oDTMem τ1 τ2).
  Global Instance Proper_cTMem l : Proper ((≡) ==> (≡) ==> (≡)) (cTMem l).
  Proof. solve_proper. Qed.

  Lemma cTMem_eq l T1 T2 d ρ :
    cTMem l T1 T2 ρ [(l, d)] ⊣⊢ oDTMem T1 T2 ρ d.
  Proof. by rewrite dty2clty_singleton. Qed.

  Definition cVMem l τ : clty Σ := dty2clty l (oDVMem τ).
  Global Instance Proper_cVMem l : Proper ((≡) ==> (≡)) (cVMem l).
  Proof. solve_proper. Qed.

  Lemma cVMem_eq l T d ρ :
    cVMem l T ρ [(l, d)] ⊣⊢ oDVMem T ρ d.
  Proof. by rewrite dty2clty_singleton. Qed.

  Lemma cVMem_dpt_eq l T p ρ :
    cVMem l T ρ [(l, dpt p)] ⊣⊢ path_wp p (oClose T ρ).
  Proof. by rewrite cVMem_eq oDVMem_eq. Qed.

  Lemma oSel_pv {n} w l args ρ v :
    oSelN n (pv w) l args ρ v ⊣⊢
      ∃ ψ d, ⌜w.[ρ] @ l ↘ d⌝ ∧ d ↗n[ n ] ψ ∧ ▷ □ ψ args v.
  Proof. by rewrite /= path_wp_pv_eq. Qed.

  Definition oSing `{!dlangG Σ} p : olty Σ 0 := olty0 (λI ρ v, ⌜alias_paths p.|[ρ] (pv v)⌝).

  (* Function types; this definition is contractive (similarly to what's
     useful for equi-recursive types). *)
  Definition oAll τ1 τ2 := olty0
    (λI ρ v,
    (∃ t, ⌜ v = vabs t ⌝ ∧
     □ ∀ w, ▷ τ1 vnil ρ w → ▷ E⟦ τ2 ⟧ (w .: ρ) t.|[w/])).

  Global Instance Proper_oAll : Proper ((≡) ==> (≡) ==> (≡)) oAll.
  Proof. solve_proper_ho. Qed.

  Definition oPrim b : olty Σ 0 := olty0 (λI ρ v, ⌜pure_interp_prim b v⌝).

  (* Observe the naming pattern for semantic type constructors:
  replace T by o (for most constructors) or by c (for constructors producing
  cltys). *)
  Global Instance dot_interp : CTyInterp Σ := fix dot_interp T :=
    let _ := dot_interp : CTyInterp Σ in
    match T with
    | TTMem l L U => cTMem l V⟦ L ⟧ V⟦ U ⟧
    | TVMem l T' => cVMem l V⟦ T' ⟧
    | TAnd T1 T2 => cAnd C⟦T1⟧ C⟦T2⟧
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

  Global Instance pinterp_lemmas: CTyInterpLemmas Σ.
  Proof.
    split; rewrite /pty_interp;
     induction T => args sb1 sb2 w; rewrite /= /pty_interp;
      properness; rewrite ?scons_up_swap ?hsubst_comp; trivial.
      by f_equiv => ?.
  Qed.

  Definition idtp  Γ T l d     := sdtp l d  V⟦Γ⟧* C⟦T⟧.
  Definition idstp Γ T ds      := sdstp ds  V⟦Γ⟧* C⟦T⟧.
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

  Implicit Types (T : olty Σ 0) (Td : clty Σ) (Tds : dslty Σ).

  Global Instance sdtp_persistent : IntoPersistent' (sdtp l d   Γ Td) | 0 := _.
  Global Instance sdstp_persistent : IntoPersistent' (sdstp ds  Γ Tds) | 0 := _.
  Global Instance setp_persistent : IntoPersistent' (setp e     Γ T) | 0 := _.
  Global Instance sstpi_persistent : IntoPersistent' (sstpi i j Γ T1 T2) | 0 := _.
  Global Instance sptp_persistent : IntoPersistent' (sptp p i   Γ T) | 0 := _.
End SemTypes.

Global Instance: Params (@oAll) 2 := {}.

Notation "d ↗ ψ" := (dm_to_type 0 d ψ) (at level 20).
Notation "G⟦ Γ ⟧ ρ" := (s⟦ V⟦ Γ ⟧* ⟧* ρ) (at level 10).

(** Single-definition typing *)
Notation "Γ ⊨ {  l := d  } : T" := (idtp Γ T l d) (at level 74, d, l, T at next level).
(** Multi-definition typing *)
Notation "Γ ⊨ds ds : T" := (idstp Γ T ds) (at level 74, ds, T at next level).
(** Expression typing *)
Notation "Γ ⊨ e : T" := (ietp Γ T e) (at level 74, e, T at next level).
Notation "Γ ⊨p p : T , i" := (iptp Γ T p i) (at level 74, p, T, i at next level).
Notation "Γ ⊨ T1 , i <: T2 , j" := (istpi Γ T1 T2 i j) (at level 74, T1, T2, i, j at next level).

Import stamp_transfer.
(** Judgment variants indexed by [gφ]. *)
Notation "Γ ⊨[ gφ  ] { l := d  } : T" := (wellMappedφ gφ → idtp Γ T l d)%I (at level 74, d, l, T at next level).
Notation "Γ ⊨ds[ gφ  ] ds : T" := (wellMappedφ gφ → idstp Γ T ds)%I (at level 74, ds, T at next level).
Notation "Γ ⊨[ gφ  ] e : T" := (wellMappedφ gφ → ietp Γ T e)%I (at level 74, e, T at next level).
Notation "Γ ⊨p[ gφ  ] p : T , i" := (wellMappedφ gφ → iptp Γ T p i)%I (at level 74, p, T, i at next level).
Notation "Γ ⊨[ gφ  ] T1 , i <: T2 , j" := (wellMappedφ gφ → istpi Γ T1 T2 i j)%I (at level 74, T1, T2, i, j at next level).

Notation oInt := (oPrim tint).
Notation oBool := (oPrim tbool).

(** Show these typing judgments are equivalent to what we present in the paper. *)
Section JudgDefs.
  Context `{HdotG: !dlangG Σ}.

  (* This is only useful to show that certain definitions we give are
    equivalent to the ones in the paper. *)
  Lemma lift_dty_vl_equiv_paper l T :
    lift_dty_vl l T ≡ lift_dty_vl_paper (lift_dty_dms l T).
  Proof.
    (* The proof is just a quantifier swap. *)
    intros args ρ v; rewrite /= /objLookup; iSplit.
    by iDestruct 1 as (d (ds & -> & Hl)) "/= H"; eauto.
    by iDestruct 1 as (ds -> d Hl) "/= H"; eauto 10.
  Qed.

  Implicit Types (T : ty) (Γ : ctx).

  Lemma path_includes_equiv p ρ ds : path_includes (pv (ids 0)) ρ ds ↔
    ∃ ds', ρ 0 = vobj ds' ∧ ds.|[ρ] `sublist_of` selfSubst ds' ∧ wf_ds ds'.
  Proof. by rewrite /path_includes path_wp_pure_pv_eq. Qed.

  Lemma idstp_eq Γ T ds : Γ ⊨ds ds : T ⊣⊢
    ⌜wf_ds ds⌝ ∧ □∀ ρ, ⌜path_includes (pv (ids 0)) ρ ds ⌝ → G⟦Γ⟧ ρ → Ds⟦T⟧ ρ ds.|[ρ].
  Proof. reflexivity. Qed.

  Lemma ietp_eq Γ e T :
    Γ ⊨ e : T ⊣⊢ □∀ ρ, G⟦Γ⟧ ρ → E⟦ V⟦T⟧ ⟧ ρ (e.|[ρ]).
  Proof. reflexivity. Qed.

  Lemma istpi_eq Γ T1 i T2 j :
    Γ ⊨ T1, i <: T2, j ⊣⊢
    □∀ ρ v, G⟦Γ⟧ ρ → ▷^i V⟦T1⟧ vnil ρ v → ▷^j V⟦T2⟧ vnil ρ v.
  Proof. reflexivity. Qed.

  Lemma iptp_eq Γ p T i :
    Γ ⊨p p : T , i ⊣⊢
    □∀ ρ, G⟦Γ⟧ ρ →
      ▷^i path_wp (p.|[ρ]) (λ v, V⟦T⟧ vnil ρ v).
  Proof. reflexivity. Qed.
End JudgDefs.

Section MiscLemmas.
  Context `{HdotG: !dlangG Σ}.
  Implicit Types (τ L T U : olty Σ 0).

  Lemma sdtp_eq (Γ : sCtx Σ) (T : clty Σ) l d:
    Γ s⊨ { l := d } : T ⊣⊢
      (□∀ ρ, ⌜path_includes (pv (ids 0)) ρ [(l, d)]⌝ → s⟦Γ⟧* ρ → T ρ [(l, d.|[ρ])]).
  Proof.
    rewrite /= pure_True ?(left_id True%I bi_and); by [> | exact: NoDup_singleton].
  Qed.

  Lemma sP_Val {Γ} v T:
    Γ s⊨ tv v : T -∗
    Γ s⊨p pv v : T, 0.
  Proof.
    iIntros "/= #Hp !>" (ρ) "Hg". rewrite path_wp_pv_eq -wp_value_inv'.
    iApply ("Hp" with "Hg").
  Qed.

  Lemma sSub_Refl {Γ} T i : ⊢ Γ s⊨ T, i <: T, i.
  Proof. by iIntros "!> **". Qed.

  Lemma sSub_Trans {Γ T1 T2 T3 i1 i2 i3} : Γ s⊨ T1, i1 <: T2, i2 -∗
                                      Γ s⊨ T2, i2 <: T3, i3 -∗
                                      Γ s⊨ T1, i1 <: T3, i3.
  Proof.
    iIntros "#Hsub1 #Hsub2 !> * #Hg #HT".
    iApply ("Hsub2" with "[//] (Hsub1 [//] [//])").
  Qed.

  Lemma sSub_Eq {Γ T U i j} :
    Γ s⊨ T, i <: U, j ⊣⊢
    Γ s⊨ oLaterN i T, 0 <: oLaterN j U, 0.
  Proof. done. Qed.

  Lemma ipwp_terminates {p T i}:
    [] s⊨p p : T , i ⊢ ▷^i ⌜ terminates (path2tm p) ⌝.
  Proof.
    iIntros "#H".
    iSpecialize ("H" $! ids with "[//]"); rewrite hsubst_id.
    iApply (path_wp_terminates with "H").
  Qed.
End MiscLemmas.

(** * Proper instances. *)
Section Propers.
  (** This instance doesn't allow setoid rewriting in the function argument
  to [iterate]. That's appropriate for this project. *)
  Global Instance: Params (@iterate) 3 := {}.
  Global Instance Proper_iterate {n} {A : ofeT} (f : A → A) :
    Proper (equiv ==> equiv) f →
    Proper (equiv ==> equiv) (iterate f n).
  Proof.
    elim: n => [|n IHn] Hp x y Heq; rewrite ?(iterate_0, iterate_S) //.
    f_equiv. exact: IHn.
  Qed.

  Context `{HdotG: !dlangG Σ}.

  (** ** Judgments *)
  Global Instance Proper_sstpi i j : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (sstpi i j).
  Proof.
    solve_proper_ho.
    (* intros ?? HG ?? H1 ?? H2; simplify_eq/=.
    properness; [by rewrite HG|apply H1|apply H2]. *)
  Qed.
  Global Instance Proper_sstpi_flip i j :
    Proper ((≡) --> (≡) --> (≡) --> flip (≡)) (sstpi i j).
  Proof. apply: flip_proper_4. Qed.
  Global Instance: Params (@sstpi) 4 := {}.


  Global Instance Proper_setp e : Proper ((≡) ==> (≡) ==> (≡)) (setp e).
  Proof.
    solve_proper_ho.
    (* intros ?? HG ?? HT ???; simplify_eq/=. by properness; [rewrite HG|apply HT]. *)
  Qed.
  Global Instance Proper_setp_flip e :
    Proper (flip (≡) ==> flip (≡) ==> flip (≡)) (setp e).
  Proof. apply: flip_proper_3. Qed.
  Global Instance: Params (@setp) 3 := {}.

  Global Instance Proper_sdstp ds : Proper ((≡) ==> (≡) ==> (≡)) (sdstp ds).
  Proof. move => ??? [?? _ _ _] [?? _ _ _] [/= ??]; properness; by f_equiv. Qed.
  Global Instance Proper_sdstp_flip ds :
    Proper (flip (≡) ==> flip (≡) ==> flip (≡)) (sdstp ds).
  Proof. apply: flip_proper_3. Qed.

  Global Instance Proper_sdtp l d : Proper ((≡) ==> (≡) ==> (≡)) (sdtp l d) := _.
  Global Instance Proper_sdtp_flip l d : Proper (flip (≡) ==> flip (≡) ==> flip (≡)) (sdtp l d) := _.
  Global Instance: Params (@sdtp) 4 := {}.

  Global Instance Proper_sptp p i : Proper ((≡) ==> (≡) ==> (≡)) (sptp p i).
  Proof. solve_proper_ho. Qed.
  Global Instance Proper_sptp_flip p i : Proper ((≡) --> (≡) --> flip (≡)) (sptp p i).
  Proof. apply: flip_proper_3. Qed.
  Global Instance: Params (@sptp) 4 := {}.
End Propers.

Section defs.
  Context `{HdotG: !dlangG Σ}.

  Lemma iterate_TLater_oLater i T:
    V⟦iterate TLater i T⟧ ≡ oLaterN i V⟦T⟧.
  Proof. elim: i => [//|i IHi] ???. by rewrite !iterate_S /= (IHi _ _ _). Qed.

  Lemma iterate_TLater_later T n args ρ v:
    V⟦ iterate TLater n T ⟧ args ρ v ⊣⊢ ▷^n V⟦ T ⟧ args ρ v.
  Proof. by rewrite (iterate_TLater_oLater n T _ _ _). Qed.

  Lemma sSub_iterate_TLater_Eq {Γ T U i j} :
    V⟦ Γ ⟧* s⊨ V⟦ T ⟧, i <: V⟦ U ⟧, j ⊣⊢
    V⟦ Γ ⟧* s⊨ V⟦ iterate TLater i T ⟧, 0 <: V⟦ iterate TLater j U ⟧, 0.
  Proof. by rewrite sSub_Eq !iterate_TLater_oLater. Qed.


  Lemma P_Val {Γ} v T: Γ ⊨ tv v : T -∗ Γ ⊨p pv v : T, 0.
  Proof. apply sP_Val. Qed.

  Lemma Sub_Refl {Γ} T i : ⊢ Γ ⊨ T, i <: T, i.
  Proof. apply sSub_Refl. Qed.

  Lemma Sub_Trans {Γ T1 T2 T3 i1 i2 i3} :
    Γ ⊨ T1, i1 <: T2, i2 -∗ Γ ⊨ T2, i2 <: T3, i3 -∗
    Γ ⊨ T1, i1 <: T3, i3.
  Proof. apply sSub_Trans. Qed.

  Lemma Sub_Eq {Γ T U i j} :
    Γ ⊨ T, i <: U, j ⊣⊢
    Γ ⊨ iterate TLater i T, 0 <: iterate TLater j U, 0.
  Proof. by rewrite /istpi sSub_iterate_TLater_Eq. Qed.
End defs.

(** Backward compatibility. *)
Notation "⟦ T ⟧" := (oClose V⟦ T ⟧).

Import dlang_adequacy.

Theorem s_adequacy_dot_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} {e Ψ}
  (τ : ∀ `{!dlangG Σ}, olty Σ 0)
  (Himpl : ∀ `(Hdlang: !dlangG Σ) v, oClose τ ids v -∗ ⌜Ψ v⌝)
  (Hlog : ∀ `(!dlangG Σ) `(!SwapPropI Σ), allGs ∅ ==∗ [] s⊨ e : τ):
  adequate e (λ v, Ψ v).
Proof.
  eapply (adequacy_dlang _); [apply Himpl | iIntros (??) "Hgs"].
  iMod (Hlog with "Hgs") as "#Htyp".
  iEval rewrite -(hsubst_id e). iApply ("Htyp" $! ids with "[//]").
Qed.

Theorem adequacy_dot_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} {e Ψ T}
  (Himpl : ∀ `(Hdlang: !dlangG Σ) v, V⟦ T ⟧ vnil ids v -∗ ⌜Ψ v⌝)
  (Hlog : ∀ `(!dlangG Σ) `(!SwapPropI Σ), allGs ∅ ==∗ [] ⊨ e : T):
  adequate e (λ v, Ψ v).
Proof. exact: (s_adequacy_dot_sem Σ (λ _, V⟦T⟧)). Qed.

Corollary s_safety_dot_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} {e}
  (τ : ∀ `{!dlangG Σ}, olty Σ 0)
  (Hwp : ∀ `{!dlangG Σ} `(!SwapPropI Σ), allGs ∅ ==∗ [] s⊨ e : τ):
  safe e.
Proof. apply adequate_safe, (s_adequacy_dot_sem Σ τ), Hwp; naive_solver. Qed.

Corollary safety_dot_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} {e T}
  (Hwp : ∀ `{!dlangG Σ} `(!SwapPropI Σ), allGs ∅ ==∗ [] ⊨ e : T):
  safe e.
Proof. exact: (s_safety_dot_sem Σ (λ _, V⟦T⟧)). Qed.

(** Adequacy of semantic typing: not only are semantically well-typed expressions safe,
but any result value they produce also satisfies any properties that follow from their
semantic type. *)
Theorem adequacy_mapped_semtyping Σ `{!dlangPreG Σ} `{!SwapPropI Σ} {e g Ψ T}
  (Himpl : ∀ `(!dlangG Σ) v, ⟦ T ⟧ ids v -∗ ⌜Ψ v⌝)
  (Hlog : ∀ `(!dlangG Σ) `(!SwapPropI Σ), ⊢ [] ⊨[ Vs⟦ g ⟧ ] e : T):
  adequate e (λ v, Ψ v).
Proof.
  eapply (adequacy_dot_sem Σ Himpl).
  iIntros (??) "Hs"; iApply Hlog. iApply (transfer_empty with "Hs").
Qed.

(** Theorem 5.5: safety of semantic typing. Corollary of [adequacy_mapped_semtyping]. *)
Corollary safety_mapped_semtyping Σ `{!dlangPreG Σ} `{!SwapPropI Σ} {e g T}
  (Hlog : ∀ `(!dlangG Σ) `(!SwapPropI Σ), ⊢ [] ⊨[ Vs⟦ g ⟧ ] e : T):
  safe e.
Proof.
  eapply adequate_safe, adequacy_mapped_semtyping, Hlog;
    naive_solver.
Qed.

(** Adequacy of normalization for gDOT paths. *)
Lemma ipwp_gs_adequacy Σ `{dlangPreG Σ} `{SwapPropI Σ} {g p T i}
  (Hwp : ∀ `(Hdlang : !dlangG Σ) `(!SwapPropI Σ), ⊢ [] ⊨p[ Vs⟦ g ⟧ ] p : T , i):
  terminates (path2tm p).
Proof.
  eapply (@soundness (iResUR Σ) _ i).
  apply (bupd_plain_soundness _).
  iMod (gen_iheap_init (L := stamp) ∅) as (hG) "Hgs".
  set (DLangΣ := DLangG Σ).
  iMod (transfer_empty (Hdlang := DLangΣ) Vs⟦ g ⟧ with "Hgs") as "Hgs".
  iApply ipwp_terminates.
  iApply (Hwp DLangΣ with "Hgs").
Qed.
