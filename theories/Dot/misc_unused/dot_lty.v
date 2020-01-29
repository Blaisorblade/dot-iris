From iris.proofmode Require Import tactics.
From D Require Export iris_prelude proper.
From D Require Import lty ty_interp_subst_lemmas pty_interp_subst_lemmas.
From D.Dot Require Import syn syn.path_repl dlang_inst path_wp lr_syn_aux.
From D.pure_program_logic Require Import lifting.

Implicit Types (Σ : gFunctors).
Implicit Types
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (vs : vls) (ρ : var → vl) (l : label).

Local Notation IntoPersistent' P := (IntoPersistent false P P).

Module SemTypes.

Include LtyJudgements VlSorts dlang_inst.
Include PTyInterpLemmas VlSorts dlang_inst.
Import persistent_ty_interp_lemmas.

(** Override notations to specify scope. *)
Notation "p⟦ T ⟧" := (pty_interp T%ty).
Notation "p⟦ Γ ⟧*" := (fmap (M := list) pty_interp Γ).

Definition dslty Σ := env -> iPPred dms Σ.
Definition dsltyO Σ := env -d> iPPredO dms Σ.
Notation Dslty T := (λ ρ, IPPred (λI ds, T ρ ds)).

Record dlty Σ := Dlty {
  dlty_label : label;
  dlty_car :> env -> iPPred dm Σ;
}.
Global Arguments Dlty {_} _%I _.
Global Arguments dlty_label {_} !_ /.
Global Arguments dlty_car {_} !_ /.

(* Forces inserting coercions to -d>. *)
Notation dApp := (dlty_car : dlty _ → _ -d> _).

Canonical Structure labelO := leibnizO label.

Section dlty_ofe.
  Context {Σ}.
  Let iso := (λ T : dlty Σ, (dApp T, dlty_label T)).
  Instance dlty_equiv : Equiv (dlty Σ) := λ A B, iso A ≡ iso B.
  Instance dlty_dist : Dist (dlty Σ) := λ n A B, iso A ≡{n}≡ iso B.
  Lemma dlty_ofe_mixin : OfeMixin (dlty Σ).
  Proof. exact: (iso_ofe_mixin iso). Qed.
End dlty_ofe.
Canonical Structure dltyO Σ := OfeT (dlty Σ) dlty_ofe_mixin.

Section defs.
  Context `{HdotG: dlangG Σ}.
  Implicit Types (T : oltyO Σ 0) (TD : dlty Σ).
  Definition mkDlty l (φ : envPred dm Σ) `{∀ ρ d, Persistent (φ ρ d)} : dlty Σ :=
    Dlty l (λ ρ, IPPred (φ ρ)).

  Definition lift_dlty (φ : dlty Σ) l : envPred dm Σ :=
    λI ρ d, ⌜ dlty_label φ = l ⌝ ∧ φ ρ d.

  Context {i : nat}.
  Implicit Types (φ : hoEnvD Σ i) (τ : olty Σ i).
  (*
    Even if semantic types use infinite substitutions, we can still reuse the
    current stamping theory, based on finite substitutions.
  *)
  Definition leadsto_envD_equiv s σ (φ : hoEnvD Σ i) : iProp Σ :=
    (∃ (φ' : hoEnvD Σ i),
      ⌜φ ≡ (λ args ρ, φ' args (∞ σ.|[ρ]))⌝ ∧ s ↝n[ i ] φ')%I.
  Arguments leadsto_envD_equiv /.

  Definition dm_to_type d i (ψ : hoD Σ i) : iProp Σ :=
    (∃ s σ, ⌜ d = dtysem σ s ⌝ ∧ s ↗n[ σ , i ] ψ)%I.
End defs.

(* Definition sdtp Γ TD l d : iProp Σ :=
  (⌜ l = dlty_label TD ⌝ ∧
    □∀ ρ, s⟦Γ⟧* ρ → TD ρ d.|[ρ])%I. *)
Definition sdtp `{HdotG: dlangG Σ} Γ (φ : dltyO Σ) l d : iProp Σ :=
  □∀ ρ, ⌜path_includes (pv (ids 0)) ρ [(l, d)] ⌝ → s⟦Γ⟧* ρ → lift_dlty φ l ρ d.|[ρ].
Global Arguments sdtp /.

(** Multi-definition typing *)
Definition sdstp `{HdotG: dlangG Σ} Γ (T : dsltyO Σ) ds : iProp Σ :=
  ⌜wf_ds ds⌝ ∧ □∀ ρ, ⌜path_includes (pv (ids 0)) ρ ds ⌝ → s⟦Γ⟧* ρ → T ρ ds.|[ρ].
Global Arguments sdstp /.

Definition sptp `{HdotG: dlangG Σ} Γ (T : oltyO Σ 0) p i: iProp Σ :=
  □∀ ρ, s⟦Γ⟧* ρ -∗
    ▷^i path_wp (p.|[ρ]) (λ v, oClose T ρ v).
Global Arguments sptp /.

Notation "Γ s⊨ {  l := d  } : T" := (sdtp Γ T l d) (at level 64, d, l, T at next level).
Notation "Γ s⊨p p : τ , i" := (sptp Γ τ p i) (at level 74, p, τ, i at next level).
Notation "s ↝[  σ  ] φ" := (leadsto_envD_equiv s σ φ) (at level 20).
Notation "d ↗n[ i  ] ψ" := (dm_to_type d i ψ) (at level 20).

Section dm_to_type.
  Context `{HdotG: dlangG Σ}.

  Global Instance dm_to_type_persistent d i ψ: Persistent (d ↗n[ i ] ψ) := _.

  Lemma dm_to_type_agree d i ψ1 ψ2 args v : d ↗n[ i ] ψ1 -∗ d ↗n[ i ] ψ2 -∗ ▷ (ψ1 args v ≡ ψ2 args v).
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

  Program Definition lift_dinterp_vl (TD : dlty Σ): olty Σ 0 :=
    olty0 (λI ρ v, ∃ d, ⌜v @ dlty_label TD ↘ d⌝ ∧ TD ρ d).

  (* Rewrite using (higher) semantic kinds! *)
  Definition oDTMem l τ1 τ2 : dlty Σ := mkDlty l
    (λI ρ d,
    ∃ ψ, (d ↗n[ 0 ] ψ) ∧
       □ ((∀ v, ▷ τ1 vnil ρ v → ▷ □ ψ vnil v) ∧
          (∀ v, ▷ □ ψ vnil v → ▷ τ2 vnil ρ v))).

  Definition oTTMem l τ1 τ2 :=
    lift_dinterp_vl (oDTMem l τ1 τ2).

  Definition oDVMem l τ : dlty Σ := mkDlty l
    (λI ρ d, ∃ pmem, ⌜d = dpt pmem⌝ ∧ path_wp pmem (oClose τ ρ)).

  Definition oTVMem l τ :=
    lift_dinterp_vl (oDVMem l τ).

  Definition oTSel p l :=
    olty0 (λI ρ v, path_wp p.|[ρ]
      (λ vp, ∃ ψ d, ⌜vp @ l ↘ d⌝ ∧ d ↗n[ 0 ] ψ ∧ ▷ □ ψ vnil v)).

  Lemma oTSel_pv w l args ρ v :
    oTSel (pv w) l args ρ v ⊣⊢
      ∃ ψ d, ⌜w.[ρ] @ l ↘ d⌝ ∧ d ↗n[ 0 ] ψ ∧ ▷ □ ψ vnil v.
  Proof. by rewrite /= path_wp_pv. Qed.

  Definition oSing p : olty Σ 0.
  Proof using HdotG. exact (olty0 (λI ρ v, ⌜alias_paths p.|[ρ] (pv v)⌝)). Defined.

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
     □ ∀ w, ▷ τ1 vnil ρ w → ▷ interp_expr τ2 (w .: ρ) t.|[w/])).

  Definition oPrim b : olty Σ 0 := olty0 (λI ρ v, ⌜pure_interp_prim b v⌝).

  Global Instance pinterp : PTyInterp ty Σ :=
    fix pinterp (T : ty) : olty Σ 0 :=
    let _ := pinterp : PTyInterp ty Σ in
    match T with
    | TTMem l L U => oTTMem l p⟦ L ⟧ p⟦ U ⟧
    | TVMem l T' => oTVMem l p⟦ T' ⟧
    | TAnd T1 T2 => oAnd p⟦ T1 ⟧ p⟦ T2 ⟧
    | TOr T1 T2 => oOr p⟦ T1 ⟧ p⟦ T2 ⟧
    | TLater T => oLater p⟦ T ⟧
    | TPrim b => oPrim b
    | TTop => oTop
    | TBot => oBot
    | TAll T1 T2 => oAll p⟦ T1 ⟧ p⟦ T2 ⟧
    | TMu T => oMu p⟦ T ⟧
    | TSel p l => oTSel p l
    | TSing p => oSing p
    end.
  Global Instance pinterp_lemmas: PTyInterpLemmas ty Σ.
  Proof.
    split => /=; induction T => args sb1 sb2 w /=;
      properness; rewrite ?scons_up_swap ?hsubst_comp; trivial; by f_equiv => ?.
  Qed.

  (* Strong sealing. *)
  Definition BAD_LABEL : label. Proof. exact "". Qed.

  Fixpoint def_interp_base (T : ty) : dlty Σ :=
    match T with
    | TTMem l L U => oDTMem l p⟦ L ⟧ p⟦ U ⟧
    | TVMem l T' => oDVMem l p⟦ T' ⟧
    | _ => mkDlty BAD_LABEL (λI _ _, False)
    end.

  Definition def_interp T l := lift_dlty (def_interp_base T) l.

  (* Definition Dslty' {Σ} (T : envPred dms Σ)
   `{∀ ρ ds, Persistent (T ρ ds)} : env -> iPPred dms Σ := Dslty T. *)

  Program Definition defs_interp_and (interp1 interp2 : dslty Σ) : dslty Σ :=
    Dslty (λI ρ ds, interp1 ρ ds ∧ interp2 ρ ds).

  Definition lift_dinterp_dms (T : dltyO Σ) : dsltyO Σ := Dslty (λI ρ ds,
    ∃ l d, ⌜ dms_lookup l ds = Some d ⌝ ∧ lift_dlty T l ρ d).

  Fixpoint defs_interp T : dslty Σ :=
    match T with
    | TAnd T1 T2 => defs_interp_and (defs_interp T1) (defs_interp T2)
    | TTop => Dslty (λI ρ ds, True)
    | _ => lift_dinterp_dms (def_interp_base T)
    end.

  Notation "d⟦ T ⟧" := (def_interp_base T%ty).
  Notation "ds⟦ T ⟧" := (defs_interp T%ty).

  Definition idtp  Γ T l d     := sdtp  p⟦Γ⟧* d⟦T⟧ l d.
  Definition idstp Γ T ds : iProp Σ := sdstp p⟦Γ⟧* ds⟦ T ⟧ ds.
  Definition ietp  Γ T e       := setp  p⟦Γ⟧* p⟦T⟧ e.
  Definition istpi Γ T1 T2 i j := sstpi p⟦Γ⟧* p⟦T1⟧ p⟦T2⟧ i j.
  Definition iptp  Γ T p i     := sptp  p⟦Γ⟧* p⟦T⟧ p i.
  (* Global Arguments idstp /. *)

  Global Instance idtp_persistent Γ T l d: IntoPersistent' (idtp Γ T l d) | 0 := _.
  Global Instance idstp_persistent Γ T ds: IntoPersistent' (idstp Γ T ds) | 0 := _.
  Global Instance ietp_persistent Γ T e : IntoPersistent' (ietp Γ T e) | 0 := _.
  Global Instance istpi_persistent Γ T1 T2 i j : IntoPersistent' (istpi Γ T1 T2 i j) | 0 := _.
  Global Instance iptp_persistent Γ T p i : IntoPersistent' (iptp Γ T p i) | 0 := _.

  Implicit Types (T : olty Σ 0) (Td : dlty Σ) (Tds : dslty Σ).

  (* Avoid auto-dropping box (and unfolding) when introducing judgments persistently. *)
  Local Notation IntoPersistent' P := (IntoPersistent false P P).
  Global Instance sdtp_persistent Γ Td l d: IntoPersistent' (sdtp Γ Td l d) | 0 := _.
  Global Instance sdstp_persistent Γ Tds ds: IntoPersistent' (sdstp Γ Tds ds) | 0 := _.
  Global Instance setp_persistent Γ T e : IntoPersistent' (setp Γ T e) | 0 := _.
  Global Instance sstpi_persistent Γ T1 T2 i j : IntoPersistent' (sstpi Γ T1 T2 i j) | 0 := _.
  Global Instance sptp_persistent Γ T p i : IntoPersistent' (sptp Γ T p i) | 0 := _.
End SemTypes.
Notation "d⟦ T ⟧" := (def_interp_base T%ty).
Notation "ds⟦ T ⟧" := (defs_interp T%ty).

Notation "d ↗ ψ" := (dm_to_type 0 d ψ) (at level 20).
Notation "p⟦ T ⟧ₑ" := (interp_expr p⟦ T ⟧).
Notation "⟦ Γ ⟧*" := s⟦ p⟦ Γ ⟧* ⟧*.

(* Notation "⟦ T ⟧ₑ" := (interp_expr p⟦ T ⟧). *)
(* Definition interp_env (Γ : ctx) : env -d> iPropO Σ := env_oltyped (pty_interp <$> Γ).
Global Arguments interp_env !_ _ /.
Notation "⟦ Γ ⟧*" := (interp_env Γ). *)
(* Notation "⟦ Γ ⟧*" := (env_oltyped (pty_interp <$> Γ)). *)

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
    lift_dlty (oDVMem l T) l ρ (dpt p) ⊣⊢
    path_wp p (oClose T ρ).
  Proof.
    rewrite /lift_dlty/=; iSplit. by iDestruct 1 as (_ pmem [= ->]) "$".
    iIntros "H"; iSplit; first done; iExists p. by auto.
  Qed.

  Context {Γ : sCtx Σ}.
  Lemma sSub_Sel L U va l i:
    Γ s⊨ tv va : oTTMem l L U, i -∗
    Γ s⊨ oLater L, i <: oTSel (pv va) l, i.
  Proof.
    iIntros "#Hva !>" (ρ v) "#Hg #HvL".
    iSpecialize ("Hva" with "Hg"). rewrite /= wp_value_inv' path_wp_pv.
    iNext.
    iDestruct "Hva" as (d Hl ψ) "#[Hlψ [#HLψ #HψU]]".
    iExists ψ, d; repeat iSplit => //. by iApply "HLψ".
  Qed.

  Lemma sSel_Sub L U va l i:
    Γ s⊨ tv va : oTTMem l L U, i -∗
    Γ s⊨ oTSel (pv va) l, i <: oLater U, i.
  Proof.
    iIntros "#Hva !>" (ρ v) "#Hg #Hψ".
    iSpecialize ("Hva" with "Hg"); rewrite /= wp_value_inv' path_wp_pv.
    iNext.
    iDestruct "Hva" as (d Hl ψ) "#[Hlψ [#HLψ #HψU]]".
    iDestruct "Hψ" as (ψ1 d1 Hva) "[Hγ #Hψ1v]".
    objLookupDet. iDestruct (dm_to_type_agree d _ _ _ vnil v with "Hlψ Hγ") as "#Hag".
    iApply "HψU" => //. iNext. by iRewrite "Hag".
  Qed.

  Lemma sD_Typ_Abs T L U s σ l:
    Γ s⊨ oLater T, 0 <: oLater U, 0 -∗
    Γ s⊨ oLater L, 0 <: oLater T, 0 -∗
    s ↝[ σ ] T -∗
    Γ s⊨ { l := dtysem σ s } : oDTMem l L U.
  Proof.
    iIntros "#HTU #HLT #Hs /= !>" (ρ Hpid) "#Hg"; iSplit => //=.
    iDestruct "Hs" as (φ Hγφ) "Hγ".
    iExists (hoEnvD_inst (σ.|[ρ]) φ); iSplit.
    by iApply (dm_to_type_intro with "Hγ").
    iModIntro; repeat iSplit; iIntros (v) "#HL"; rewrite later_intuitionistically.
    - iIntros "!>". iApply Hγφ. by iApply "HLT".
    - iApply "HTU" => //. by iApply Hγφ.
  Qed.

  Lemma sD_Typ (τ : olty Σ 0) s σ l:
    s ↝[ σ ] τ -∗
    Γ s⊨ { l := dtysem σ s } : oDTMem l τ τ.
  Proof. iIntros "#Hs"; iApply sD_Typ_Abs; by [| iIntros "!> **"]. Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂ᶻ
     ----------------------------------------------- (<:-μ-X)
     Γ ⊨ μ (x: T₁ˣ) <: μ(x: T₂ˣ)
  *)
  (* Notation "◁ n T ▷" := (iterate TLater n T). *)
  Lemma sSub_Mu_X T1 T2 i j:
    iterate oLater i T1 :: Γ s⊨ T1, i <: T2, j -∗
    Γ s⊨ oMu T1, i <: oMu T2, j.
  Proof.
    iIntros "/= #Hstp !>" (vs v) "#Hg #HT1".
    iApply ("Hstp" $! (v .: vs) v with "[# $Hg] [#//]").
    by rewrite s_iterate_TLater_later.
  Qed.

  Lemma sSub_Mu_A T i: Γ s⊨ oMu (shift T), i <: T, i.
  Proof. iIntros "!> **". by rewrite s_interp_TMu_ren. Qed.

  Lemma sSub_Mu_B T i: Γ s⊨ T, i <: oMu (shift T), i.
  Proof. iIntros "!> **". by rewrite s_interp_TMu_ren. Qed.

  (*
     Γ ⊨ z: Tᶻ
     =============================================== (T-Rec-I/T-Rec-E)
     Γ ⊨ z: mu(x: Tˣ)
   *)
  Lemma sTMu_equiv T v: (Γ s⊨ tv v : oMu T) ≡ (Γ s⊨ tv v : T.|[v/]).
  Proof.
    iSplit; iIntros "#Htp !>" (vs) "#Hg !> /=";
    iDestruct (wp_value_inv' with "(Htp Hg)") as "{Htp} Hgoal";
    rewrite -wp_value/= (hoEnvD_subst_one _ v (v.[vs])); done.
  Qed.

  (*
     Γ ⊨ z: Tᶻ
     =============================================== (T-Rec-I/T-Rec-E)
     Γ ⊨ z: mu(x: Tˣ)
   *)
  Lemma sTMu_I T v: Γ s⊨ tv v : T.|[v/] -∗ Γ s⊨ tv v : oMu T.
  Proof. by rewrite sTMu_equiv. Qed.

  Lemma sTMu_E T v: Γ s⊨ tv v : oMu T -∗ Γ s⊨ tv v : T.|[v/].
  Proof. by rewrite sTMu_equiv. Qed.

  Lemma sT_Forall_E e1 e2 T1 T2:
    Γ s⊨ e1 : oAll T1 (shift T2) -∗
    Γ s⊨ e2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ s⊨ tapp e1 e2 : T2.
  Proof.
    iIntros "/= #He1 #Hv2 !>" (vs) "#HG !>".
    smart_wp_bind (AppLCtx (e2.|[_])) v "#Hr" ("He1" with "[]").
    smart_wp_bind (AppRCtx v) w "#Hw" ("Hv2" with "[]").
    iDestruct "Hr" as (t ->) "#Hv".
    rewrite -wp_pure_step_later // -wp_mono /=; first by iSpecialize ("Hv" with "Hw"); iNext.
    iIntros (v); by rewrite /= (hoEnvD_weaken_one T2 _ _ _).
  Qed.

  Lemma sT_Forall_Ex e1 v2 T1 T2:
    Γ s⊨ e1: oAll T1 T2 -∗
    Γ s⊨ tv v2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ s⊨ tapp e1 (tv v2) : T2.|[v2/].
  Proof.
    iIntros "/= #He1 #Hv2Arg !> * #HG !>".
    smart_wp_bind (AppLCtx (tv v2.[_])) v "#Hr {He1}" ("He1" with "[#//]").
    iDestruct "Hr" as (t ->) "#HvFun".
    rewrite -wp_pure_step_later; last done.
    iSpecialize ("HvFun" with "[#]"). {
      rewrite -wp_value_inv'. by iApply ("Hv2Arg" with "[]").
    }
    iNext. iApply wp_wand.
    - iApply "HvFun".
    - iIntros (v) "{HG HvFun Hv2Arg} H".
      rewrite /= (hoEnvD_subst_one T2 v2 v) //.
  Qed.

  Lemma pty_interp_subst (T : ty) σ : p⟦ T.|[σ] ⟧ ≡ (p⟦ T ⟧).|[σ].
  Proof. intros ???; apply interp_subst_compose_ind. Qed.
End SampleTypingLemmas.

Module ty_compat.

Include TyInterpLemmas VlSorts dlang_inst.
Notation "⟦ T ⟧" := (ty_interp T%ty).

Ltac solve_proper_ho_equiv_core tac :=
  solve [repeat intro; cbn; repeat tac (); cbn in *;
  repeat match goal with H : _ ≡ _|- _ => apply H || rewrite H // end].
Ltac solve_proper_ho_equiv :=
  solve_proper_prepare; properness => //;
  solve_proper_ho_equiv_core ltac:(fun _ => idtac).

Section defs.
  Context `{HdotG: dlangG Σ}.

  (* Wrap this into ty_interp to reuse lemmas. *)
  Global Instance pto_ty_interp : TyInterp ty Σ := flip pty_interp vnil.
  Global Instance interp_persistent T ρ v : Persistent (⟦ T ⟧ ρ v) := _.

  Global Arguments pto_ty_interp _ /.
  Global Arguments ty_interp {_ _ _} _ /.

  Global Instance interp_lemmas: TyInterpLemmas ty Σ.
  Proof. split => /= *; apply persistent_ty_interp_lemmas.interp_subst_compose_ind. Qed.

  Lemma def_interp_tvmem_eq' l (T : ty) p ρ:
    def_interp (TVMem l T) l ρ (dpt p) ⊣⊢
    path_wp p (⟦ T ⟧ ρ).
  Proof. apply def_interp_tvmem_eq. Qed.

  (* Lemma swap0 T σ args ρ v : p⟦ T.|[σ] ⟧ args ρ v ≡ (p⟦ T ⟧).|[σ] args ρ v.
  Proof. apply persistent_ty_interp_lemmas.interp_subst_compose_ind. Qed. *)

  Global Instance Proper_env_oltyped : Proper ((≡) ==> (=) ==> (≡)) (env_oltyped (Σ := Σ)).
  Proof.
    move => + + /equiv_Forall2 + + _ <-.
    elim => [|T1 G1 IHG1] [|T2 G2] /=; [done|inversion 1..|] =>
      /(Forall2_cons_inv _ _ _ _) [HT HG] ρ; f_equiv; [apply IHG1, HG|apply HT].
  Qed.

  Global Instance Proper_sstpi :
    Proper ((≡) ==> (≡) ==> (≡) ==> (=) ==> (=) ==> (≡)) (sstpi (Σ := Σ)).
  Proof.
    solve_proper_ho_equiv.
    (* intros ?? HG ?? H1 ?? H2 ?** ?**; simplify_eq/=.
    properness; [by rewrite HG|apply H1|apply H2]. *)
  Qed.
  Global Instance Proper_sstpi_flip :
    Proper ((≡) --> (≡) --> (≡) --> (=) --> (=) --> flip (≡)) (sstpi (Σ := Σ)).
  Proof. apply: flip_proper_6. Qed.


  Global Instance Proper_setp : Proper ((≡) ==> (≡) ==> (=) ==> (≡)) setp.
  Proof.
    solve_proper_ho_equiv.
    (* intros ?? HG ?? HT ???; simplify_eq/=. by properness; [rewrite HG|apply HT]. *)
  Qed.
  Global Instance Proper_setp_flip :
    Proper (flip (≡) ==> flip (≡) ==> flip (=) ==> flip (≡)) setp.
  Proof. apply: flip_proper_4. Qed.

  Global Instance: Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (≡)) (lift_dlty (Σ := Σ)).
  Proof.
    rewrite /lift_dlty => -[l1 P1] [l2 P2] [/= Heq ?] ??? ??? ???; simplify_eq.
    solve_proper_ho_equiv.
    (* properness; [done|apply Heq]. *)
  Qed.

  Global Instance Proper_sdtp Γ : Proper ((≡) ==> (=) ==> (=) ==> (≡)) (sdtp Γ).
  Proof.
    solve_proper_ho_equiv.
    (* intros ?? Heq ??? ???; simplify_eq/=. by properness; [done..|rewrite Heq]. *)
  Qed.
  Global Instance Proper_sdtp_flip Γ : Proper (flip (≡) ==> flip (=) ==> flip (=) ==> flip (≡)) (sdtp (Σ := Σ) Γ).
  Proof. apply: flip_proper_4. Qed.

  Global Instance Proper_oAll : Proper ((≡) ==> (≡) ==> (≡)) oAll.
  Proof. solve_proper_ho_equiv. Qed.

  Lemma T_Var Γ x τ
    (Hlook : Γ !! x = Some τ):
    (*──────────────────────*)
    Γ ⊨ of_val (ids x) : shiftN x τ.
  Proof.
    rewrite /ietp (pty_interp_subst τ (ren (+x))). apply sT_Var.
    by rewrite list_lookup_fmap Hlook.
  Qed.

  Lemma iterate_TLater_oLater i T:
    p⟦iterate TLater i T⟧ ≡ iterate oLater i p⟦T⟧.
  Proof. elim: i => [//|i IHi] ???. by rewrite !iterate_S /= (IHi _ _ _). Qed.

  Lemma Sub_Mu_X Γ T1 T2 i j:
    iterate TLater i T1 :: Γ ⊨ T1, i <: T2, j -∗
    Γ ⊨ TMu T1, i <: TMu T2, j.
  Proof.
    rewrite /istpi -sSub_Mu_X.
    by rewrite fmap_cons (iterate_TLater_oLater i T1).
  Qed.
  Context {Γ : ctx}.

  Lemma TMu_I T v: Γ ⊨ tv v : T.|[v/] -∗ Γ ⊨ tv v : TMu T.
  Proof. by rewrite /ietp -sTMu_I pty_interp_subst. Qed.

  Lemma TMu_E T v: Γ ⊨ tv v : TMu T -∗ Γ ⊨ tv v : T.|[v/].
  Proof. by rewrite /ietp sTMu_E pty_interp_subst. Qed.

  Global Instance: Params (@bi_entails) 1 := {}.
  Global Instance: Params (@oAll) 2 := {}.
  (* Moving eq paramaters first would speed things up. *)
  Global Instance: Params (@setp) 2 := {}.

  Lemma T_Forall_E e1 e2 T1 T2:
    Γ ⊨ e1 : TAll T1 (shift T2) -∗
    Γ ⊨ e2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ ⊨ tapp e1 e2 : T2.
  Proof.
    rewrite /ietp -(sT_Forall_E e1 e2).
    (* apply equiv_entails. *)
    by rewrite -(pty_interp_subst T2 (ren(+1))).
    (* do 3 (properness => //=);
      apply (pty_interp_subst T2 (ren(+1))). *)
  Qed.

  Lemma T_Forall_Ex e1 v2 T1 T2:
    Γ ⊨ e1: TAll T1 T2 -∗
    Γ ⊨ tv v2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ ⊨ tapp e1 (tv v2) : T2.|[v2/].
  Proof. rewrite /ietp (sT_Forall_Ex e1 v2). by rewrite (pty_interp_subst T2). Qed.
End defs.

End ty_compat.

From D Require Import swap_later_impl.
Import dlang_adequacy adequacy ty_compat.
Theorem s_adequacy_dot_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} e Ψ
  (τ : ∀ `{dlangG Σ}, olty Σ 0)
  (Himpl : ∀ (Hdlang: dlangG Σ) v, oClose τ ids v -∗ ⌜Ψ v⌝)
  (Hlog : ∀ `{dlangG Σ} `(!SwapPropI Σ), allGs ∅ ==∗ [] s⊨ e : τ):
  ∀ σ, adequate NotStuck e σ (λ v _, Ψ v).
Proof.
  eapply (adequacy_dlang _); [apply Himpl | iIntros (??) "Hgs"].
  iMod (Hlog with "Hgs") as "#Htyp".
  iEval rewrite -(hsubst_id e). iApply ("Htyp" $! ids with "[//]").
Qed.

Theorem adequacy_dot_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} e Ψ T
  (Himpl : ∀ (Hdlang: dlangG Σ) v, ⟦ T ⟧ ids v -∗ ⌜Ψ v⌝)
  (Hlog : ∀ `{dlangG Σ} `(!SwapPropI Σ), allGs ∅ ==∗ [] ⊨ e : T):
  ∀ σ, adequate NotStuck e σ (λ v _, Ψ v).
Proof. exact: (s_adequacy_dot_sem Σ e Ψ (λ _, p⟦T⟧)). Qed.

Corollary s_safety_dot_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} e
  (τ : ∀ `{dlangG Σ}, olty Σ 0)
  (Hwp : ∀ `{dlangG Σ} `(!SwapPropI Σ), allGs ∅ ==∗ [] s⊨ e : τ):
  safe e.
Proof. apply adequate_safe, (s_adequacy_dot_sem _ e _ τ), Hwp; naive_solver. Qed.

Corollary safety_dot_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} e T
  (Hwp : ∀ `{dlangG Σ} `(!SwapPropI Σ), allGs ∅ ==∗ [] ⊨ e : T):
  safe e.
Proof. exact: (s_safety_dot_sem Σ e (λ _, p⟦T⟧)). Qed.
End SemTypes.
