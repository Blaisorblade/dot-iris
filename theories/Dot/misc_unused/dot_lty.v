From iris.proofmode Require Import tactics.
From D Require Export iris_prelude proper lty lr_syn_aux.
From D Require Import pty_interp_subst_lemmas swap_later_impl.
From D.Dot Require Import syn syn.path_repl dlang_inst path_wp.
From D.pure_program_logic Require Import lifting.

Implicit Types (Σ : gFunctors).
Implicit Types
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (vs : vls) (ρ : var → vl) (l : label).

Local Notation IntoPersistent' P := (IntoPersistent false P P).

Include LtyJudgements VlSorts dlang_inst.
Include PTyInterpLemmas VlSorts dlang_inst.
Export persistent_ty_interp_lemmas.

(** Override notations to specify scope. *)
Notation "V⟦ T ⟧" := (pty_interpO T%ty).
Notation "V⟦ Γ ⟧*" := (fmap (M := list) pty_interpO Γ).

Definition dlty Σ := env -> iPPred dm Σ.
Definition dltyO Σ := env -d> iPPredO dm Σ.
Notation Dlty T := (λ ρ, IPPred (λI d, T ρ d)).

Definition dslty Σ := env -> iPPred dms Σ.
Definition dsltyO Σ := env -d> iPPredO dms Σ.
Notation Dslty T := (λ ρ, IPPred (λI ds, T ρ ds)).

Record ldlty Σ := LDlty {
  ldlty_label : option label;
  ldlty_car :> env -> iPPred dm Σ;
}.
Global Arguments LDlty {_} _%I _.
Global Arguments ldlty_label {_} !_ /.
Global Arguments ldlty_car {_} !_ /.

Canonical Structure labelO := leibnizO label.

Section ldlty_ofe.
  Context {Σ}.
  Let iso := (λ T : ldlty Σ, (ldlty_car T : _ -d> _, ldlty_label T)).
  Instance ldlty_equiv : Equiv (ldlty Σ) := λ A B, iso A ≡ iso B.
  Instance ldlty_dist : Dist (ldlty Σ) := λ n A B, iso A ≡{n}≡ iso B.
  Lemma ldlty_ofe_mixin : OfeMixin (ldlty Σ).
  Proof. exact: (iso_ofe_mixin iso). Qed.

  Definition LDltyO ol (P : env -d> iPPredO dm Σ) := LDlty ol P.
  Global Instance: Params (@LDltyO) 2 := {}.
  Global Instance : Proper ((≡) ==> (≡)) (LDltyO ol).
  Proof. by solve_proper_prepare. Qed.
End ldlty_ofe.
Canonical Structure ldltyO Σ := OfeT (ldlty Σ) ldlty_ofe_mixin.

Record ldslty {Σ} := LDslty {
  ldslty_car :> env -> iPPred dms Σ;
  ldslty_olty :> oltyO Σ 0;
  ldslty_commute {ds ρ} :
    ldslty_car ρ (selfSubst ds) ⊢ ldslty_olty vnil ρ (vobj ds);
  ldslty_mono {l d ds ρ} :
    dms_hasnt ds l →
    ldslty_car ρ ds ⊢ ldslty_car ρ ((l, d) :: ds)
}.
Arguments ldslty : clear implicits.
Arguments LDslty {_} _ _ _ _.
Arguments ldslty_car {_} !_ /.
Arguments ldslty_olty {_} !_ /.

Section ldslty_ofe.
  Context {Σ}.
  Let iso := (λ T : ldslty Σ, (ldslty_car T : _ -d> _, ldslty_olty T)).
  Instance ldslty_equiv : Equiv (ldslty Σ) := λ A B, iso A ≡ iso B.
  Instance ldslty_dist : Dist (ldslty Σ) := λ n A B, iso A ≡{n}≡ iso B.
  Lemma ldslty_ofe_mixin : OfeMixin (ldslty Σ).
  Proof. exact: (iso_ofe_mixin iso). Qed.

  (* Definition LDsltyO (P : env -d> iPPredO dm Σ) := LDslty P.
  Global Instance : Proper ((≡) ==> (≡)) (LDltyO ol).
  Proof. by solve_proper_prepare. Qed. *)
End ldslty_ofe.
Canonical Structure ldsltyO Σ := OfeT (ldslty Σ) ldslty_ofe_mixin.

Section defs.
  Context `{HdotG: dlangG Σ}.
  Implicit Types (T : oltyO Σ 0) (TD : ldlty Σ).
  Definition mkDlty (φ : envPred dm Σ) `{∀ ρ d, Persistent (φ ρ d)} : dlty Σ :=
    Dlty (λ ρ, IPPred (φ ρ)).
  (* Definition mkLDlty optl (φ : envPred dm Σ) `{∀ ρ d, Persistent (φ ρ d)} : ldlty Σ :=
    LDlty optl (λ ρ, IPPred (φ ρ)). *)

  Definition lift_ldlty `{dlangG Σ} l ρ d (φ : ldlty Σ) : iProp Σ :=
    ⌜ ldlty_label φ = Some l ⌝ ∧ φ ρ d.

  Definition dm_to_type d i (ψ : hoD Σ i) : iProp Σ :=
    (∃ s σ, ⌜ d = dtysem σ s ⌝ ∧ s ↗n[ σ , i ] ψ)%I.
End defs.

(* Definition sdtp Γ TD l d : iProp Σ :=
  (⌜ l = ldlty_label TD ⌝ ∧
    □∀ ρ, s⟦Γ⟧* ρ → TD ρ d.|[ρ])%I. *)
Definition sdtp `{HdotG: dlangG Σ} l d  Γ (φ : ldltyO Σ): iProp Σ :=
  □∀ ρ, ⌜path_includes (pv (ids 0)) ρ [(l, d)] ⌝ → s⟦Γ⟧* ρ → lift_ldlty l ρ d.|[ρ] φ.
Global Arguments sdtp /.

(** Multi-definition typing *)
Definition sdstp `{HdotG: dlangG Σ} ds Γ (T : dsltyO Σ) : iProp Σ :=
  ⌜wf_ds ds⌝ ∧ □∀ ρ, ⌜path_includes (pv (ids 0)) ρ ds ⌝ → s⟦Γ⟧* ρ → T ρ ds.|[ρ].
Global Arguments sdstp /.

Definition sptp `{HdotG: dlangG Σ} p i Γ (T : oltyO Σ 0): iProp Σ :=
  □∀ ρ, s⟦Γ⟧* ρ -∗
    ▷^i path_wp (p.|[ρ]) (λ v, oClose T ρ v).
Global Arguments sptp /.

Notation "Γ s⊨ {  l := d  } : T" := (sdtp l d Γ T) (at level 64, d, l, T at next level).
Notation "Γ s⊨p p : τ , i" := (sptp p i Γ τ) (at level 74, p, τ, i at next level).
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

  Program Definition lift_dinterp_vl l (TD : dltyO Σ): oltyO Σ 0 :=
    olty0 (λI ρ v, ∃ d, ⌜v @ l ↘ d⌝ ∧ TD ρ d).
  Global Instance Proper_lift_dinterp_vl l : Proper ((≡) ==> (≡)) (lift_dinterp_vl l).
  Proof. solve_proper_ho_equiv. Qed.

  Definition lift_dinterp_dms `{dlangG Σ} (T : ldltyO Σ) : dsltyO Σ := Dslty (λI ρ ds,
    ∃ l d, ⌜ dms_lookup l ds = Some d ⌝ ∧ lift_ldlty l ρ d T).

  Lemma sem_lift_dinterp_dms_vl_commute (T : ldltyO Σ) ds ρ l
    (Hl : ldlty_label T = Some l) :
    lift_dinterp_dms T ρ (selfSubst ds) -∗
    lift_dinterp_vl l T vnil ρ (vobj ds).
  Proof.
    iDestruct 1 as (?l d ?) "[% H]"; simplify_eq/=.
    iExists d; iFrame. by iExists ds.
  Qed.

  Lemma lift_dinterp_dms_mono T l ρ d ds:
    dms_hasnt ds l →
    lift_dinterp_dms T ρ ds -∗ lift_dinterp_dms T ρ ((l, d) :: ds).
  Proof.
    intros ?. iDestruct 1 as (l' d' ?) "#H".
    iExists l', d'. iSplit; auto using dms_lookup_mono.
  Qed.

  Program Definition LDsLift `{dlangG Σ} l (T : ldltyO Σ)
    (Hl : ldlty_label T = Some l) : ldsltyO Σ :=
    LDslty (lift_dinterp_dms T) (lift_dinterp_vl l T) _ _.
  Next Obligation. intros. exact: sem_lift_dinterp_dms_vl_commute. Qed.
  Next Obligation. intros. exact: lift_dinterp_dms_mono. Qed.

  Program Definition LDsTop : ldslty Σ := LDslty (Dslty (λI _ _, True)) oTop _ _.
  Solve All Obligations with done.

  Program Definition LDsBot : ldslty Σ := LDslty (Dslty (λI _ _, False)) oBot _ _.
  Solve All Obligations with done.

  Program Definition LDsAnd (Tds1 Tds2 : ldslty Σ): ldslty Σ :=
    LDslty (Dslty (λI ρ ds, Tds1 ρ ds ∧ Tds2 ρ ds)) (oAnd Tds1 Tds2) _ _.
  Next Obligation. intros; iIntros "/= [??]". iSplit; by iApply ldslty_commute. Qed.
  Next Obligation. intros; iIntros "/= [??]". iSplit; by iApply ldslty_mono. Qed.


  (* Rewrite using (higher) semantic kinds! *)
  Definition oDTMem τ1 τ2 : dltyO Σ := mkDlty (λI ρ d,
    ∃ ψ, (d ↗n[ 0 ] ψ) ∧
       □ ((∀ v, ▷ τ1 vnil ρ v → ▷ □ ψ vnil v) ∧
          (∀ v, ▷ □ ψ vnil v → ▷ τ2 vnil ρ v))).
  Global Instance Proper_oDTMem : Proper ((≡) ==> (≡) ==> (≡)) oDTMem.
  Proof. solve_proper_ho_equiv. Qed.

  Definition oLDTMem l T1 T2 := LDlty (Some l) (oDTMem T1 T2).
  Global Instance Proper_oLDTMem : Proper ((≡) ==> (≡) ==> (≡)) (oLDTMem l).
  Proof. solve_proper. Qed.

  Definition oTMem l τ1 τ2 := lift_dinterp_vl l (oDTMem τ1 τ2).
  Global Instance Proper_oTMem : Proper ((≡) ==> (≡) ==> (≡)) (oTMem l).
  Proof. solve_proper_ho_equiv. Qed.

  Definition oDVMem τ : dltyO Σ := mkDlty (λI ρ d,
    ∃ pmem, ⌜d = dpt pmem⌝ ∧ path_wp pmem (oClose τ ρ)).
  Global Instance Proper_oDVMem : Proper ((≡) ==> (≡)) oDVMem.
  Proof. solve_proper_ho_equiv. Qed.

  Definition oLDVMem l T := LDlty (Some l) (oDVMem T).
  Global Instance Proper_oLDVMem : Proper ((≡) ==> (≡)) (oLDVMem l).
  Proof. solve_proper. Qed.
  Definition oVMem l τ := lift_dinterp_vl l (oDVMem τ).
  Global Instance Proper_oVMem : Proper ((≡) ==> (≡)) (oVMem l).
  Proof. solve_proper_ho_equiv. Qed.

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
  Global Instance: Params (@oAll) 2 := {}.

  Definition oPrim b : olty Σ 0 := olty0 (λI ρ v, ⌜pure_interp_prim b v⌝).

  (* Observe the naming pattern for semantic type constructors:
  replace T by o. *)
  Global Instance pinterp : PTyInterp ty Σ :=
    fix pinterp (T : ty) : olty Σ 0 :=
    let _ := pinterp : PTyInterp ty Σ in
    match T with
    | TTMem l L U => oTMem l V⟦ L ⟧ V⟦ U ⟧
    | TVMem l T' => oVMem l V⟦ T' ⟧
    | TAnd T1 T2 => oAnd V⟦ T1 ⟧ V⟦ T2 ⟧
    | TOr T1 T2 => oOr V⟦ T1 ⟧ V⟦ T2 ⟧
    | TLater T => oLater V⟦ T ⟧
    | TPrim b => oPrim b
    | TTop => oTop
    | TBot => oBot
    | TAll T1 T2 => oAll V⟦ T1 ⟧ V⟦ T2 ⟧
    | TMu T => oMu V⟦ T ⟧
    | TSel p l => oSel p l
    | TSing p => oSing p
    end.
  Global Instance pinterp_lemmas: PTyInterpLemmas ty Σ.
  Proof.
    split => /=; induction T => args sb1 sb2 w /=;
      properness; rewrite ?scons_up_swap ?hsubst_comp; trivial; by f_equiv => ?.
  Qed.

  Lemma sem_def2defs_head {T l ρ d ds}:
    lift_ldlty l ρ d T -∗
    lift_dinterp_dms T ρ ((l, d) :: ds).
  Proof. iIntros; iExists l, d. auto using dms_lookup_head. Qed.

  Fixpoint def_interp_base (T : ty) : dlty Σ :=
    match T with
    | TTMem l L U => oDTMem V⟦ L ⟧ V⟦ U ⟧
    | TVMem l T' => oDVMem V⟦ T' ⟧
    | _ => mkDlty (λI _ _, False)
    end.
  Notation "D*⟦ T ⟧" := (def_interp_base T).
  Definition ldef_interp T := LDlty (label_of_ty T) D*⟦ T ⟧.
  Notation "LD⟦ T ⟧" := (ldef_interp T).
  Definition def_interp T l ρ d := lift_ldlty l ρ d LD⟦ T ⟧.
  Notation "D[ l ]⟦ T ⟧" := (def_interp T l).

  Program Definition defs_interp_and (interp1 interp2 : dslty Σ) : dslty Σ :=
    Dslty (λI ρ ds, interp1 ρ ds ∧ interp2 ρ ds).

  Reserved Notation "Ds⟦ T ⟧".
  Fixpoint defs_interp T : dslty Σ :=
    match T with
    | TAnd T1 T2 => defs_interp_and Ds⟦T1⟧ Ds⟦T2⟧
    | TTop => Dslty (λI ρ ds, True)
    | _ => lift_dinterp_dms (LD⟦ T ⟧)
    end
  where "Ds⟦ T ⟧" := (defs_interp T).

  Reserved Notation "LDs⟦ T ⟧".
  Fixpoint ldefs_interp T : ldslty Σ :=
    match T with
    | TAnd T1 T2 => LDsAnd LDs⟦T1⟧ LDs⟦T2⟧
    | TTop => LDsTop
    (* | _ => lift_dinterp_dms (LD⟦ T ⟧) *)
    | _ => LDsBot
    end
  where "LDs⟦ T ⟧" := (ldefs_interp T).

  Lemma lift_dinterp_dms_vl_commute T ds ρ l:
    label_of_ty T = Some l →
    lift_dinterp_dms LD⟦T⟧ ρ (selfSubst ds) -∗
    lift_dinterp_vl l D*⟦T⟧ vnil ρ (vobj ds).
  Proof. apply (sem_lift_dinterp_dms_vl_commute LD⟦ T ⟧). Qed.
  (* Lemma def2defs_head {T l ρ d ds}:
    D[ l ]⟦T⟧ ρ d -∗ lift_dinterp_dms LD⟦T⟧ ρ ((l, d) :: ds).
  Proof. apply sem_def2defs_head. Qed. *)

  Lemma def2defs_head {l d ds ρ T} :
    lift_ldlty l ρ d LD⟦ T ⟧ ⊢ Ds⟦ T ⟧ ρ ((l, d) :: ds).
  Proof.
    iIntros "#HT". iPoseProof "HT" as (Hl) "_".
    destruct T; simplify_eq/=; iApply (sem_def2defs_head with "HT").
  Qed.

  Lemma lift_dsinterp_dms_vl_commute T ds ρ:
    Ds⟦T⟧ ρ (selfSubst ds) -∗
    V⟦T⟧ vnil ρ (vobj ds).
  Proof.
    iIntros "H /=".
    iInduction T as [] "IHT";
      try iDestruct "H" as (???) "[_[]]"; first done.
    - iDestruct "H" as "/= [#H1 #H2]".
      by iSplit; [> iApply "IHT"| iApply "IHT1"].
    - by rewrite (lift_dinterp_dms_vl_commute (TVMem _ _)).
    - by rewrite (lift_dinterp_dms_vl_commute (TTMem _ _ _)).
  Qed.

  Lemma defs_interp_mono T l ρ d ds:
    dms_hasnt ds l →
    Ds⟦T⟧ ρ ds -∗
    Ds⟦T⟧ ρ ((l, d) :: ds).
  Proof.
    iIntros (Hlds) "HT".
    iInduction T as [] "IHT" => //=;
      try by [iDestruct "HT" as (????) "?" | iApply lift_dinterp_dms_mono].
    iDestruct "HT" as "[HT1 HT2]"; iSplit; by [>iApply "IHT"|iApply "IHT1"].
  Qed.

  Definition idtp  Γ T l d     := sdtp l d  V⟦Γ⟧* LD⟦T⟧.
  Definition idstp Γ T ds      := sdstp ds  V⟦Γ⟧* Ds⟦T⟧.
  Definition ietp  Γ T e       := setp e    V⟦Γ⟧* V⟦T⟧.
  Definition istpi Γ T1 T2 i j := sstpi i j V⟦Γ⟧* V⟦T1⟧ V⟦T2⟧.
  Definition iptp  Γ T p i     := sptp p i  V⟦Γ⟧* V⟦T⟧.
  (* Global Arguments idstp /. *)

  Global Instance idtp_persistent Γ T l d: IntoPersistent' (idtp Γ T l d) | 0 := _.
  Global Instance idstp_persistent Γ T ds: IntoPersistent' (idstp Γ T ds) | 0 := _.
  Global Instance ietp_persistent Γ T e : IntoPersistent' (ietp Γ T e) | 0 := _.
  Global Instance istpi_persistent Γ T1 T2 i j : IntoPersistent' (istpi Γ T1 T2 i j) | 0 := _.
  Global Instance iptp_persistent Γ T p i : IntoPersistent' (iptp Γ T p i) | 0 := _.

  Implicit Types (T : olty Σ 0) (Td : ldlty Σ) (Tds : dslty Σ).

  (* Avoid auto-dropping box (and unfolding) when introducing judgments persistently. *)
  Global Instance sdtp_persistent : IntoPersistent' (sdtp l d   Γ Td) | 0 := _.
  Global Instance sdstp_persistent : IntoPersistent' (sdstp ds  Γ Tds) | 0 := _.
  Global Instance setp_persistent : IntoPersistent' (setp e     Γ T) | 0 := _.
  Global Instance sstpi_persistent : IntoPersistent' (sstpi i j Γ T1 T2) | 0 := _.
  Global Instance sptp_persistent : IntoPersistent' (sptp p i   Γ T) | 0 := _.
End SemTypes.

Section ldslty_defs.
  Context `{dlangG Σ}.
End ldslty_defs.

Notation "D*⟦ T ⟧" := (def_interp_base T).
Notation "LD⟦ T ⟧" := (ldef_interp T).
Notation "D[ l ]⟦ T ⟧" := (def_interp T l).
Notation "Ds⟦ T ⟧" := (defs_interp T).

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
(** Single-definition typing *)
Notation "Γ ⊨[ gφ  ] { l := d  } : T" := (wellMappedφ gφ → idtp Γ T l d)%I (at level 74, d, l, T at next level).
(** Multi-definition typing *)
Notation "Γ ⊨ds[ gφ  ] ds : T" := (wellMappedφ gφ → idstp Γ T ds)%I (at level 74, ds, T at next level).
(** Expression typing *)
Notation "Γ ⊨[ gφ  ] e : T" := (wellMappedφ gφ → ietp Γ T e)%I (at level 74, e, T at next level).
Notation "Γ ⊨p[ gφ  ] p : T , i" := (wellMappedφ gφ → iptp Γ T p i)%I (at level 74, p, T, i at next level).
Notation "Γ ⊨[ gφ  ] T1 , i <: T2 , j" := (wellMappedφ gφ → istpi Γ T1 T2 i j)%I (at level 74, T1, T2, i, j at next level).

Section SampleTypingLemmas.
  Context `{HdotG: dlangG Σ}.
  Implicit Types (τ L T U : olty Σ 0).

  Lemma def_interp_tvmem_eq l T p ρ :
    lift_ldlty l ρ (dpt p) (oLDVMem l T) ⊣⊢
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
End SampleTypingLemmas.

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

  Global Instance Proper_lift_ldlty l ρ d : Proper ((≡) ==> (≡)) (lift_ldlty l ρ d).
  Proof. move => [l1 P1] [l2 P2] [/= Heq]. solve_proper_ho_equiv. Qed.
  Global Instance: Params (@lift_ldlty) 5 := {}.

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
    solve_proper_ho_equiv.
    (* intros ?? Heq ??? ???; simplify_eq/=. by properness; [done..|rewrite Heq]. *)
  Qed.
  Global Instance Proper_sdtp_flip l d : Proper (flip (≡) ==> flip (≡) ==> flip (≡)) (sdtp l d).
  Proof. apply: flip_proper_3. Qed.
  Global Instance: Params (@sdtp) 4 := {}.

End Propers.

Section defs.
  Context `{HdotG: dlangG Σ}.

  (* We don't expose the binding lemmas on this wrapper, only on the
     underlying interface. *)
  (* Global Instance interp_lemmas: TyInterpLemmas ty Σ.
  Proof. split => /= *; apply persistent_ty_interp_lemmas.interp_subst_compose_ind. Qed. *)

  Lemma def_interp_tvmem_eq' l (T : ty) p ρ:
    D[ l ]⟦ TVMem l T ⟧ ρ (dpt p) ⊣⊢
    path_wp p (V⟦ T ⟧ vnil ρ).
  Proof. apply def_interp_tvmem_eq. Qed.

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

  Lemma T_Var x τ
    (Hlook : Γ !! x = Some τ):
    (*──────────────────────*)
    Γ ⊨ of_val (ids x) : shiftN x τ.
  Proof.
    rewrite /ietp (pty_interp_subst τ (ren (+x))). apply sT_Var.
    by rewrite list_lookup_fmap Hlook.
  Qed.


  (* Global Instance: Params (@bi_entails) 1 := {}.
   *)
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
