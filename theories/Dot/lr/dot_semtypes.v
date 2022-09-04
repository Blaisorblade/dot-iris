(** * Logical relation and semantic judgments. *)
From D Require Export iris_prelude proper lty lr_syn_aux.
From D Require Import iris_extra.det_reduction.
From D Require Import swap_later_impl.
From D.Dot Require Import syn path_repl.
From D.Dot Require Export dlang_inst path_wp.
From D.pure_program_logic Require Import weakestpre.

From D.Dot Require Export dot_lty sem_kind_dot.

Unset Program Cases.
Set Suggest Proof Using.

Implicit Types (Σ : gFunctors)
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : env) (l : label).

(** ** Define fully semantic judgments. They accept arbitrary semantic types. *)

Section judgments.
  Context {Σ}.
  Implicit Types (τ : oltyO Σ).

  (** Expression typing *)
  Definition setp `{!dlangG Σ} e Γ τ : iProp Σ :=
    |==> ∀ ρ, sG⟦Γ⟧* ρ → sE⟦ τ ⟧ ρ (e.|[ρ]).
  #[global] Arguments setp : simpl never.

  (** Delayed subtyping. *)
  Definition sstpd `{!dlangG Σ} i Γ τ1 τ2 : iProp Σ :=
    |==> ∀ ρ,
      sG⟦Γ⟧*ρ → ▷^i (oClose τ1 ρ ⊆ oClose τ2 ρ).
  #[global] Arguments sstpd : simpl never.

  (** Multi-definition typing *)
  Definition sdstp `{!dlangG Σ} ds Γ (T : clty Σ) : iProp Σ :=
    |==> ⌜wf_ds ds⌝ ∧ ∀ ρ, ⌜path_includes (pv (ids 0)) ρ ds ⌝ → sG⟦Γ⟧* ρ → T ρ ds.|[ρ].
  #[global] Arguments sdstp : simpl never.

  (** Definition typing *)
  Definition sdtp `{!dlangG Σ} l d Γ (φ : clty Σ) : iProp Σ := sdstp [(l, d)] Γ φ.
  #[global] Arguments sdtp : simpl never.

  (** Path typing *)
  Definition sptp `{!dlangG Σ} p i Γ τ : iProp Σ :=
    |==> ∀ ρ, sG⟦Γ⟧* ρ →
      ▷^i path_wp p.|[ρ] (oClose τ ρ).
  #[global] Arguments sptp : simpl never.
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
  Context `{HdotG : !dlangG Σ}.

  Lemma sstpd_eq_1 Γ T1 i T2 :
    Γ s⊨ T1 <:[i] T2 ⊣⊢
    |==> ∀ ρ, sG⟦Γ⟧* ρ → ∀ v, ▷^i (T1 anil ρ v → T2 anil ρ v).
  Proof.
    rewrite /sstpd /subtype_lty; f_equiv; f_equiv => ρ.
    by rewrite laterN_forall.
  Qed.

  Lemma sstpd_eq Γ T1 i T2 :
    Γ s⊨ T1 <:[i] T2 ⊣⊢
    |==> ∀ ρ v, sG⟦Γ⟧* ρ → ▷^i (T1 anil ρ v → T2 anil ρ v).
  Proof. rewrite sstpd_eq_1; properness. apply: forall_swap_impl. Qed.
End JudgEqs.

(** ** gDOT semantic types. *)
Definition vl_sel `{!dlangG Σ} vp l args v `{!RecTyInterp Σ} : iProp Σ :=
  ∃ d ψ, ⌜vp ,, l ↘ d⌝ ∧ d ↗ ψ ∧ packHoLtyO ψ args v.

Definition oSel `{!dlangG Σ} p l `{!RecTyInterp Σ} : oltyO Σ :=
  Olty (λI args ρ v, path_wp p.|[ρ] (λ vp, vl_sel vp l args v)).

Section sel_types_lemmas.
  Context `{HdotG : !dlangG Σ}.

  #[global] Instance vl_sel_contractive vp l args v : Contractive (@vl_sel _ _ vp l args v).
  Proof. solve_contractive_ho. Qed.
  (* Deducible. *)
  Definition vl_sel_ne vp l args v : NonExpansive (@vl_sel _ _ vp l args v) :=
    contractive_ne _.
  #[global] Instance vl_sel_proper vp l args v : Proper1 (@vl_sel _ _ vp l args v) :=
    ne_proper _.

  #[global] Instance oSel_contractive p l : Contractive (@oSel _ _ p l).
  Proof.
    move=> n ri1 ri2 Hri args ρ v /=.
    f_equiv => w.
    solve_contractive_ho.
  Qed.
  Definition oSel_ne p l : NonExpansive (@oSel _ _ p l) :=
    contractive_ne _.
  #[global] Instance oSel_proper p l : Proper1 (@oSel _ _ p l) :=
    ne_proper _.
End sel_types_lemmas.

Section sem_types.
  Context `{HdotG : !dlangG Σ}.
  Implicit Types (τ : oltyO Σ).

  (** [ D⟦ { a : τ } ⟧ ]. *)
  Definition oDVMem τ : dltyO Σ := Dlty (λI ρ d,
    ∃ pmem, ⌜d = dpt pmem⌝ ∧ path_wp pmem (oClose τ ρ)).
  #[global] Instance oDVMem_ne : NonExpansive oDVMem.
  Proof. solve_proper_ho. Qed.
  #[global] Instance oDVMem_proper : Proper1 oDVMem :=
    ne_proper _.

  Lemma oDVMem_eq T ρ p :
    oDVMem T ρ (dpt p) ≡ path_wp p (oClose T ρ).
  Proof. simpl; iSplit; last by eauto. by iDestruct 1 as (pmem [= ->]) "$". Qed.

  (** Define [cVMem] by lifting [oDVMem] to [clty]s. *)

  (** [ Ds⟦ { l : τ } ⟧] and [ V⟦ { l : τ } ⟧ ]. *)
  Definition cVMem l τ : clty Σ := dty2clty l (oDVMem τ).
  #[global] Instance cVMem_ne l : NonExpansive (cVMem l).
  Proof. solve_proper. Qed.
  #[global] Instance cVMem_proper l : Proper1 (cVMem l) :=
    ne_proper _.

  Lemma cVMem_eq l T d ρ :
    cVMem l T ρ [(l, d)] ⊣⊢ oDVMem T ρ d.
  Proof. apply dty2clty_singleton. Qed.

  (** [ V⟦ p.type ⟧]. *)
  Definition oSing `{!dlangG Σ} p : olty Σ := olty0 (λI ρ v, ⌜alias_paths p.|[ρ] (pv v)⌝).

  (** [ V⟦ ∀ x: τ1. τ2 ⟧]. *)
  (* Function types; this definition is contractive (similarly to what's
     useful for equi-recursive types). *)
  Definition oAll τ1 τ2 := olty0
    (λI ρ v,
    (∃ t, ⌜ v = vabs t ⌝ ∧
     ∀ w, ▷ τ1 anil ρ w → ▷ sE⟦ τ2 ⟧ (w .: ρ) t.|[w/])).

  #[global] Instance oAll_ne : NonExpansive2 oAll.
  Proof. solve_proper_ho. Qed.

  #[global] Instance oAll_proper : Proper2 oAll :=
    ne_proper_2 _.

  (** Semantics of primitive types. *)
  Definition oPrim b : olty Σ := olty0 (λI ρ v, ⌜pure_interp_prim b v⌝).

End sem_types.

#[global] Instance : Params (@oAll) 2 := {}.

Notation oInt := (oPrim tint).
Notation oBool := (oPrim tbool).

(** Semantics of type members in the ICFP'20 paper:
[ Ds⟦ { l >: τ1 <: τ2 } ⟧] and [ V⟦ { l >: τ1 <: τ2 } ⟧ ]. *)
Notation cTMemL l L U := (cTMem l (oLater L) (oLater U)).
Notation oTMemL l L U := (clty_olty (cTMemL l L U)).
Notation oVMem l τ := (clty_olty (cVMem l τ)).

Section misc_lemmas.
  Context `{HdotG : !dlangG Σ} `{!RecTyInterp Σ}.
  Implicit Types (τ L T U : olty Σ).

  Lemma oSel_pv w l args ρ v :
    oSel (pv w) l args ρ v ⊣⊢
      ∃ d ψ, ⌜w.[ρ] ,, l ↘ d⌝ ∧ d ↗ ψ ∧ ▷ ψ args v.
  Proof. by rewrite /= path_wp_pv_eq. Qed.

  Lemma oVMem_eq l T anil ρ v :
    oVMem l T anil ρ v ⊣⊢
    ∃ pmem, ⌜v ,, l ↘ dpt pmem⌝ ∧ path_wp pmem (oClose T ρ).
  Proof.
    etrans; [apply bi_exist_nested_swap|]; apply bi.exist_proper => p.
    rewrite and2_exist_r.
    apply bi.and_proper, reflexivity; iIntros "!% /="; naive_solver.
  Qed.

  (** Core lemmas about type selections and bounds. *)
  Lemma vl_sel_ub w l L U ρ v :
    vl_sel w l anil v -∗
    oTMem l L U anil ρ w -∗
    U anil ρ v.
  Proof.
    rewrite oTMem_unfold.
    iIntros "Hφ"; iDestruct 1 as (d1 Hl1 φ1) "(Hdφ1 & _ & HφU)".
    iApply "HφU".
    iDestruct "Hφ" as (d2 φ2 Hl2) "[Hdφ2 Hφ2v]".
    objLookupDet; iDestruct (dm_to_type_agree anil v with "Hdφ2 Hdφ1") as "Hag".
    iNext. by iRewrite "Hag" in "Hφ2v".
  Qed.

  Lemma vl_sel_lb w l L U ρ v :
    L anil ρ v -∗
    oTMem l L U anil ρ w -∗
    vl_sel w l anil v.
  Proof.
    rewrite oTMem_unfold.
    iIntros "HL"; iDestruct 1 as (d Hl φ) "[Hdφ [HLφ _]]".
    iExists d, φ; iFrame (Hl) "Hdφ". iApply ("HLφ" with "HL").
  Qed.

  Lemma lift_sub_dty2cltyN i (T1 T2 : dlty Σ) l ρ :
    (∀ d, ▷^i T1 ρ d -∗ ▷^i T2 ρ d) ⊢
    oLaterN i (lift_dty_vl l T1) anil ρ ⊆ oLaterN i ((lift_dty_vl l T2)) anil ρ.
  Proof.
    iIntros "Hsub %v". iDestruct 1 as (d) "[Hl #H1]"; iExists d; iFrame "Hl".
    by iApply ("Hsub" with "H1").
  Qed.

  Lemma lift_sub_dty2clty (T1 T2 : dlty Σ) l ρ :
    (∀ d, T1 ρ d -∗ T2 ρ d) ⊢
    lift_dty_vl l T1 anil ρ ⊆ lift_dty_vl l T2 anil ρ.
  Proof. apply (lift_sub_dty2cltyN 0). Qed.

  Lemma oDTMem_respects_sub L1 L2 U1 U2 ρ d :
    L2 anil ρ ⊆ L1 anil ρ -∗
    U1 anil ρ ⊆ U2 anil ρ -∗
    oDTMem L1 U1 ρ d -∗ oDTMem L2 U2 ρ d.
  Proof.
    rewrite !oDTMem_unfold.
    iIntros "#HsubL #HsubU"; iDestruct 1 as (φ) "#(Hφl & #HLφ & #HφU)".
    iExists φ; iSplit; first done; iSplit; iIntros "%w #Hw".
    - iApply ("HLφ" with "(HsubL Hw)").
    - iApply ("HsubU" with "(HφU Hw)").
  Qed.

  Lemma oTMem_respects_sub L1 L2 U1 U2 ρ l :
    L2 anil ρ ⊆ L1 anil ρ -∗
    U1 anil ρ ⊆ U2 anil ρ -∗
    oTMem l L1 U1 anil ρ ⊆ oTMem l L2 U2 anil ρ.
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
    oLaterN i (oVMem l T1) anil ρ ⊆ oLaterN i (oVMem l T2) anil ρ.
  Proof.
    rewrite -lift_sub_dty2cltyN. iIntros "Hsub %d".
    iApply (oDVMem_respects_subN with "Hsub").
  Qed.
  Definition oVMem_respects_sub := oVMem_respects_subN 0.

  Lemma sdtp_eq (Γ : sCtx Σ) (T : clty Σ) l d :
    Γ s⊨ { l := d } : T ⊣⊢
      |==> ∀ ρ, ⌜path_includes (pv (ids 0)) ρ [(l, d)]⌝ → sG⟦Γ⟧* ρ → T ρ [(l, d.|[ρ])].
  Proof.
    rewrite /sdtp /sdstp pure_True ?(left_id _ bi_and);
      by [> | exact: NoDup_singleton].
  Qed.

  Lemma sdtp_eq' (Γ : sCtx Σ) (T : dlty Σ) l d :
    Γ s⊨ { l := d } : dty2clty l T ⊣⊢
      |==> ∀ ρ, ⌜path_includes (pv (ids 0)) ρ [(l, d)]⌝ → sG⟦Γ⟧* ρ → T ρ d.|[ρ].
  Proof. by rewrite sdtp_eq; properness; last apply dty2clty_singleton. Qed.

  Lemma ipwp_terminates {p T i} :
    [] s⊨p p : T , i ⊢ |==> ▷^i ⌜ terminates (path2tm p) ⌝.
  Proof.
    iIntros ">#H".
    iSpecialize ("H" $! ids with "[//]"); rewrite hsubst_id.
    iApply (path_wp_terminates with "H").
  Qed.

  (** This typing lemma is here to be usable in proof of other lemmas. *)
  Lemma sT_Path {Γ τ p} :
    Γ s⊨p p : τ, 0 -∗ Γ s⊨ path2tm p : τ.
  Proof.
    iIntros ">#Hep !> %ρ #Hg /="; rewrite path2tm_subst.
    by iApply (path_wp_to_wp with "(Hep Hg)").
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

  Lemma rewrite_path_path_repl {p q p1 p2 ρ v} :
    p1 ~pp[ p := q ] p2 →
    alias_paths p.|[ρ] q.|[ρ] → (* p : q.type *)
    ⌜alias_paths p1.|[ρ] (pv v)⌝ ⊣⊢@{iPropI Σ} ⌜alias_paths p2.|[ρ] (pv v)⌝.
    (* alias_paths p1.|[ρ] (pv v) ↔ alias_paths p2.|[ρ] (pv v). *)
  Proof using Type*.
    intros Hrew Hal.
    rewrite !alias_paths_pv_eq_1 -!path_wp_pureable.
    exact: path_replacement_equiv.
  Qed.
End path_repl_lemmas.

(** Proper instances. *)

(** This instance doesn't allow setoid rewriting in the function argument
to [iterate]. That's appropriate for this project. *)
#[global] Instance : Params (@iterate) 3 := {}.
#[global] Instance iterate_proper {n} {A : ofe} (f : A → A) :
  Proper (equiv ==> equiv) f →
  Proper (equiv ==> equiv) (iterate f n).
Proof.
  elim: n => [|n IHn] Hp x y Heq; rewrite ?(iterate_0, iterate_S) //.
  f_equiv. exact: IHn.
Qed.

Section Propers.
  Context `{HdotG : !dlangG Σ}.

  (** Judgments *)
  #[global] Instance sstpd_proper i : Proper3 (sstpd i).
  Proof.
    solve_proper_ho.
    (* intros ?? HG ?? H1 ?? H2; rewrite /sstpd /subtype_lty;
    properness; [by rewrite HG|apply H1|apply H2]. *)
  Qed.
  #[global] Instance : Params (@sstpd) 3 := {}.

  #[global] Instance setp_proper e : Proper2 (setp e).
  Proof.
    solve_proper_ho.
    (* intros ?? HG ?? HT ???; simplify_eq/=. by properness; [rewrite HG|apply HT]. *)
  Qed.
  #[global] Instance : Params (@setp) 3 := {}.

  #[global] Instance sdstp_proper ds : Proper2 (sdstp ds).
  Proof.
    rewrite /sdstp => ??? [?? _] [?? _] [/= ??]; properness; by f_equiv.
  Qed.
  #[global] Instance : Params (@sdstp) 3 := {}.

  #[global] Instance sdtp_proper l d : Proper2 (sdtp l d) := _.
  #[global] Instance : Params (@sdtp) 4 := {}.

  #[global] Instance sptp_proper p i : Proper2 (sptp p i).
  Proof. solve_proper_ho. Qed.
  #[global] Instance : Params (@sptp) 4 := {}.
End Propers.
