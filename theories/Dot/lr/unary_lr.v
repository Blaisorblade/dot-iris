From iris.proofmode Require Import tactics.
From D Require Export iris_prelude proper lty lr_syn_aux.
From D Require Import swap_later_impl.
From D.Dot Require Import syn.
From D.Dot Require Export dlang_inst path_wp.
From D.pure_program_logic Require Import weakestpre.

From D.Dot Require Export dot_lty.

Unset Program Cases.

Implicit Types (Σ : gFunctors)
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (vs : vls) (ρ : var → vl) (l : label).

(** * Semantic domains. *)

(** The logical relation core is [V⟦T⟧], which interprets *open* types into
    predicates over *closed* values. Hence, [V⟦T⟧ T args ρ v] uses its argument [ρ]
    to interpret anything contained in T, but not things contained in v.

    Semantic judgements must apply instead to open terms/value/paths; therefore,
    they are defined using closing substitution on arguments of [interp].

    Similar comments apply to [def_interp].

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
  Definition setp `{dlangG Σ} e Γ τ : iProp Σ :=
    □∀ ρ, s⟦Γ⟧* ρ → E⟦ τ ⟧ ρ (e.|[ρ]).
  Global Arguments setp /.

  (** Indexed subtyping. *)
  Definition sstpi `{dlangG Σ} i j Γ τ1 τ2 : iProp Σ :=
    □∀ ρ v,
      s⟦Γ⟧*ρ → ▷^i oClose τ1 ρ v → ▷^j oClose τ2 ρ v.
  Global Arguments sstpi /.

  (** Definition typing *)
  Definition sdtp `{dlangG Σ} l d Γ (φ : clty Σ): iProp Σ :=
    □∀ ρ, ⌜path_includes (pv (ids 0)) ρ [(l, d)] ⌝ → s⟦Γ⟧* ρ → lift_ldlty (clty_dlty φ) ρ l d.|[ρ].
  Global Arguments sdtp /.

  (** Multi-definition typing *)
  Definition sdstp `{dlangG Σ} ds Γ (T : clty Σ) : iProp Σ :=
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

  (* Rewrite using (higher) semantic kinds! *)
  Definition oLDTMem l τ1 τ2 : ldltyO Σ := mkLDlty (Some l) (λI ρ d,
    ∃ ψ, d ↗n[ 0 ] ψ ∧
       □ ((∀ v, ▷ τ1 vnil ρ v → ▷ □ ψ vnil v) ∧
          (∀ v, ▷ □ ψ vnil v → ▷ τ2 vnil ρ v))).
  Global Instance Proper_oLDTMem l : Proper ((≡) ==> (≡) ==> (≡)) (oLDTMem l).
  Proof. rewrite /oLDTMem/= => ??? ???. f_equiv. solve_proper_ho. Qed.

  Definition oLDVMem l τ : ldltyO Σ := mkLDlty (Some l) (λI ρ d,
    ∃ pmem, ⌜d = dpt pmem⌝ ∧ path_wp pmem (oClose τ ρ)).
  Global Instance Proper_oLDVMem l : Proper ((≡) ==> (≡)) (oLDVMem l).
  Proof. rewrite /oLDVMem/= => ???. f_equiv. solve_proper_ho. Qed.

  (** [cTMem] and [cVMem] are full [clty]. *)
  Definition cTMem l τ1 τ2 : clty Σ := ldlty2clty (oLDTMem l τ1 τ2).
  Global Instance Proper_cTMem l : Proper ((≡) ==> (≡) ==> (≡)) (cTMem l).
  Proof. solve_proper. Qed.

  Definition cVMem l τ : clty Σ := ldlty2clty (oLDVMem l τ).
  Global Instance Proper_cVMem l : Proper ((≡) ==> (≡)) (cVMem l).
  Proof. solve_proper. Qed.

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
  Proof. solve_proper_ho. Qed.

  Definition oPrim b : olty Σ 0 := olty0 (λI ρ v, ⌜pure_interp_prim b v⌝).

  (* Observe the naming pattern for semantic type constructors:
  replace T by o. *)
  Global Program Instance dot_interp : DTyInterp Σ := fix dot_interp T :=
    let _ := dot_interp : DTyInterp Σ in
    match T with
    | TTMem l L U => cTMem l V⟦ L ⟧ V⟦ U ⟧
    | TVMem l T' => cVMem l V⟦ T' ⟧

    | TAnd T1 T2 => cAnd A⟦T1⟧ A⟦T2⟧

    | TTop => cTop
    | TBot => olty2clty oBot

    | TOr T1 T2 => olty2clty $ oOr V⟦ T1 ⟧ V⟦ T2 ⟧
    | TLater T => olty2clty $ oLater V⟦ T ⟧
    | TPrim b => olty2clty $ oPrim b
    | TAll T1 T2 => olty2clty $ oAll V⟦ T1 ⟧ V⟦ T2 ⟧
    | TMu T => olty2clty $ oMu V⟦ T ⟧
    | TSel p l => olty2clty $ oSel p l
    | TSing p => olty2clty $ oSing p
    end.

  Global Instance pinterp_lemmas: PTyInterpLemmas Σ.
  Proof.
    split; rewrite /pty_interp;
     induction T => args sb1 sb2 w; rewrite /= /pty_interp;
      properness; rewrite ?scons_up_swap ?hsubst_comp; trivial.
      by f_equiv => ?.
  Qed.

  Lemma ld_label_match T : ldlty_label LD⟦ T ⟧ = label_of_ty T.
  Proof. by destruct T. Qed.

  Definition idtp  Γ T l d     := sdtp l d  V⟦Γ⟧* A⟦T⟧.
  Definition idstp Γ T ds      := sdstp ds  V⟦Γ⟧* A⟦T⟧.
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
End SemTypes.

Global Instance: Params (@oAll) 2 := {}.

Section clty_defs.
  Context `{dlangG Σ}.
End clty_defs.

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

  Global Instance Proper_sdtp l d : Proper ((≡) ==> (≡) ==> (≡)) (sdtp l d).
  Proof.
    move => ??? [??? _ _ _] [??? _ _ _] [[/=?[/=??]]?];
      repeat case_match; simplify_eq/=; properness => //; solve_proper_ho.
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
Notation "⟦ T ⟧" := (V⟦ T ⟧ vnil).
