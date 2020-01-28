From iris.proofmode Require Import tactics.
From D Require Export iris_prelude.
From D Require Import ty_interp_subst_lemmas lty.
From D.Dot Require Import syn syn.path_repl dlang_inst path_wp lr_syn_aux.
From D.pure_program_logic Require Import lifting.

Notation "'λI' x .. y , t" := (fun x => .. (fun y => t%I) ..)
  (at level 200, x binder, y binder, right associativity, only parsing,
  format "'[  ' '[  ' 'λI'  x  ..  y ']' ,  '/' t ']'") : function_scope.

Include TyInterpLemmas VlSorts dlang_inst.

(** Override notation from [dlang] to specify scope. *)
Notation "⟦ T ⟧" := (ty_interp T%ty).

Implicit Types (Σ : gFunctors).
Implicit Types
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (vs : vls) (ρ : var → vl).

Module SemTypes.

Include LtyJudgements VlSorts dlang_inst.

Record dlty Σ := Dlty {
  dlty_label : label;
  dlty_car : env -d> dm -d> iPropO Σ;
  dlty_persistent ρ d :> Persistent (dlty_car ρ d);
}.
Global Arguments Dlty {_} _%I _ {_}.
Global Arguments dlty_car {_} !_ _ _ /.
Global Arguments dlty_label {_} _ /.
Global Existing Instance dlty_persistent.

Local Notation IntoPersistent' P := (IntoPersistent false P P).

Section Defs.
  Context `{HdotG: dlangG Σ} {i : nat}.
  Implicit Types (φ : hoEnvD Σ i) (τ : olty Σ i).
  Implicit Types (T : olty Σ 0) (TD : dlty Σ).

  Definition lift_dlty (φ : dlty Σ) l : envPred dm Σ :=
    λI ρ d, ⌜ dlty_label φ = l ⌝ ∧ dlty_car φ ρ d.

  (* Definition sdtp Γ l (φ : dlty Σ) d : iProp Σ :=
    □∀ ρ, ⌜path_includes (pv (ids 0)) ρ [(l, d)] ⌝ → s⟦Γ⟧* ρ → lift_dlty φ l ρ d.|[ρ]. *)

  Definition sdtp Γ TD l d : iProp Σ :=
    (⌜ l = dlty_label TD ⌝ ∧
      □∀ ρ, s⟦Γ⟧* ρ → dlty_car TD ρ d.|[ρ])%I.
  Global Arguments sdtp /.

  Definition sptp Γ T p i: iProp Σ :=
    □∀ ρ, s⟦Γ⟧* ρ -∗
      ▷^i path_wp (p.|[ρ]) (λ v, oClose T ρ v).

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
End Defs.

Notation "Γ s⊨ { l := d  } : T" := (sdtp Γ T l d) (at level 64, d, l, T at next level).
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

  Implicit Types (τ : olty Σ 0).
   (* (ψ : vl -d> iPropO Σ) (φ : envD Σ)  *)

  Program Definition lift_dinterp_vl (T : dlty Σ): olty Σ 0 :=
    olty0 (λI ρ v, (∃ d, ⌜v @ dlty_label T ↘ d⌝ ∧ dlty_car T ρ d)).

  (* Rewrite using (higher) semantic kinds! *)
  Definition oDTMem l τ1 τ2 : dlty Σ := Dlty l
    (λI ρ d,
    ∃ ψ, (d ↗n[ 0 ] ψ) ∧
       □ ((∀ v, ▷ τ1 vnil ρ v → ▷ □ ψ vnil v) ∧
          (∀ v, ▷ □ ψ vnil v → ▷ τ2 vnil ρ v))).

  Definition oTTMem l τ1 τ2 :=
    lift_dinterp_vl (oDTMem l τ1 τ2).

  Definition oDVMem l τ : dlty Σ := Dlty l
    (λI ρ d, ∃ pmem, ⌜d = dpt pmem⌝ ∧ path_wp pmem (oClose τ ρ)).

  Definition oTVMem l τ :=
    lift_dinterp_vl (oDVMem l τ).

  Definition oTSel p (l : label) :=
    olty0 (λI ρ v, path_wp p.|[ρ]
      (λ vp, ∃ ψ d, ⌜vp @ l ↘ d⌝ ∧ d ↗n[ 0 ] ψ ∧ ▷ □ ψ vnil v)).

  Lemma oTSel_pv w (l : label) args ρ v :
    oTSel (pv w) l args ρ v ⊣⊢
      ∃ ψ d, ⌜w.[ρ] @ l ↘ d⌝ ∧ d ↗n[ 0 ] ψ ∧ ▷ □ ψ vnil v.
  Proof. by rewrite /= path_wp_pv. Qed.

  Definition oPSing p : olty Σ 0 :=
    olty0 (λI ρ v, ⌜alias_paths p.|[ρ] (pv v)⌝).

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
  Definition oForall τ1 τ2 := olty0
    (λI ρ v,
    (∃ t, ⌜ v = vabs t ⌝ ∧
     □ ∀ w, ▷ τ1 vnil ρ w → ▷ interp_expr τ2 (w .: ρ) t.|[w/])).

  Definition oPrim b : olty Σ 0 := olty0 (λI ρ v, ⌜pure_interp_prim b v⌝).

  Class PersTyInterp (ty : Type) Σ :=
    pers_ty_interp : ty → olty Σ 0.
  Notation "p⟦ T ⟧" := (pers_ty_interp T%ty).
  Global Arguments pers_ty_interp {_ _ _} !_ /.

  Global Instance pinterp : PersTyInterp ty Σ :=
    fix pinterp (T : ty) : olty Σ 0 :=
    let _ := pinterp : PersTyInterp ty Σ in
    match T with
    | TTMem l L U => oTTMem l p⟦ L ⟧ p⟦ U ⟧
    | TVMem l T' => oTVMem l p⟦ T' ⟧
    | TAnd T1 T2 => oAnd p⟦ T1 ⟧ p⟦ T2 ⟧
    | TOr T1 T2 => oOr p⟦ T1 ⟧ p⟦ T2 ⟧
    | TLater T => oLater p⟦ T ⟧
    | TPrim b => oPrim b
    | TTop => oTop
    | TBot => oBot
    | TAll T1 T2 => oForall p⟦ T1 ⟧ p⟦ T2 ⟧
    | TMu T => oMu p⟦ T ⟧
    | TSel p l => oTSel p l
    | TSing p => oPSing p
    end.
  (* Wrap this into ty_interp to reuse lemmas. *)
  Global Instance pers_to_ty_interp : TyInterp ty Σ := flip pers_ty_interp vnil.
  Global Arguments pers_to_ty_interp _ /.
  Global Arguments ty_interp {_ _ _} _ /.

  Global Instance interp_lemmas: TyInterpLemmas ty Σ.
  Proof.
    split => /=; induction T => sb1 sb2 w /=;
      properness; rewrite ?scons_up_swap ?hsubst_comp; trivial; by f_equiv => ?.
  Qed.

  Global Instance interp_persistent T ρ v : Persistent (⟦ T ⟧ ρ v) := _.

  Fixpoint def_interp_base (T : ty) : dlty Σ :=
    match T with
    | TTMem l L U => oDTMem l p⟦ L ⟧ p⟦ U ⟧
    | TVMem l T' => oDVMem l p⟦ T' ⟧
    | _ => Dlty "" (λI _ _, False)
    end.

  Global Instance def_interp_persistent T ρ d :
    Persistent (dlty_car (def_interp_base T) ρ d).
  Proof. destruct T; try apply _. Qed.

  Implicit Types (l : label).

  Definition def_interp T l := lift_dlty (def_interp_base T) l.

  Definition defs_interp_and (interp1 interp2 : envPred dms Σ) : envPred dms Σ :=
    λI ρ ds, interp1 ρ ds ∧ interp2 ρ ds.

  Definition lift_dinterp_dms T : envPred dms Σ := λI ρ ds,
    ∃ l d, ⌜ dms_lookup l ds = Some d ⌝ ∧ def_interp T l ρ d.

  Fixpoint defs_interp T : envPred dms Σ :=
    match T with
    | TAnd T1 T2 => defs_interp_and (defs_interp T1) (defs_interp T2)
    | TTop => λI ρ ds, True
    | _ => lift_dinterp_dms T
    end.

  Global Instance defs_interp_persistent T ρ ds : Persistent (defs_interp T ρ ds).
  Proof. induction T; try apply _. Qed.

  (** Multi-definition typing *)
  Definition idstp Γ T ds : iProp Σ :=
    ⌜wf_ds ds⌝ ∧ □∀ ρ, ⌜path_includes (pv (ids 0)) ρ ds ⌝ → s⟦Γ⟧* ρ → defs_interp T ρ ds.|[ρ].
  Global Arguments idstp /.

  (* Fixpoint interp_env (Γ : ctx) (ρ : var → vl) : iProp Σ :=
    match Γ with
    | T :: Γ' => interp_env Γ' (stail ρ) ∧ ⟦ T ⟧ ρ (shead ρ)
    | nil => True
    end%I. *)

  Notation "p⟦ Γ ⟧*" := (pers_ty_interp <$> Γ).
  Notation "d⟦ T ⟧" := (def_interp_base T%ty).

  Definition idtp  Γ T l d     := sdtp  p⟦Γ⟧* d⟦T⟧ l d.
  (* Definition idstp Γ T ds      := sdstp p⟦Γ⟧* p⟦T⟧ ds. *)
  Definition ietp  Γ T e       := setp  p⟦Γ⟧* p⟦T⟧ e.
  Definition istpi Γ T1 T2 i j := sstpi p⟦Γ⟧* p⟦T1⟧ p⟦T2⟧ i j.
  Definition iptp  Γ T p i     := sptp  p⟦Γ⟧* p⟦T⟧ p i.

  Global Instance idtp_persistent Γ T l d: IntoPersistent' (idtp Γ T l d) | 0 := _.
  Global Instance idstp_persistent Γ T ds: IntoPersistent' (idstp Γ T ds) | 0 := _.
  Global Instance ietp_persistent Γ T e : IntoPersistent' (ietp Γ T e) | 0 := _.
  Global Instance istpi_persistent Γ T1 T2 i j : IntoPersistent' (istpi Γ T1 T2 i j) | 0 := _.
  Global Instance iptp_persistent Γ T p i : IntoPersistent' (iptp Γ T p i) | 0 := _.

  Implicit Types (T : olty Σ 0) (TD : dlty Σ).

  Local Notation IntoPersistent' P := (IntoPersistent false P P).
  (* Avoid auto-dropping box (and unfolding) when introducing judgments persistently. *)
  Global Instance sdtp_persistent Γ TD l d: IntoPersistent' (sdtp Γ TD l d) | 0 := _.
  (* Global Instance sdstp_persistent Γ T ds: IntoPersistent' (sdstp Γ T ds) | 0 := _. *)
  Global Instance setp_persistent Γ T e : IntoPersistent' (setp Γ T e) | 0 := _.
  Global Instance sstpi_persistent Γ T1 T2 i j : IntoPersistent' (sstpi Γ T1 T2 i j) | 0 := _.
  Global Instance sptp_persistent Γ T p i : IntoPersistent' (sptp Γ T p i) | 0 := _.

End SemTypes.
Notation "d ↗ ψ" := (dm_to_type 0 d ψ) (at level 20).
Notation "p⟦ T ⟧" := (pers_ty_interp T%ty).
Notation "p⟦ Γ ⟧*" := (pers_ty_interp <$> Γ).
Notation "p⟦ T ⟧ₑ" := (interp_expr ⟦ T ⟧).
(* Notation "⟦ T ⟧ₑ" := (interp_expr p⟦ T ⟧). *)
(* Definition interp_env (Γ : ctx) : env -d> iPropO Σ := env_oltyped (pers_ty_interp <$> Γ).
Global Arguments interp_env !_ _ /.
Notation "⟦ Γ ⟧*" := (interp_env Γ). *)
(* Notation "⟦ Γ ⟧*" := (env_oltyped (pers_ty_interp <$> Γ)). *)
Notation "⟦ Γ ⟧*" := s⟦ p⟦ Γ ⟧* ⟧*.


(** Single-definition typing *)
Notation "Γ ⊨ {  l := d  } : T" := (idtp p⟦Γ⟧* p⟦T⟧ l d) (at level 74, d, l, T at next level).
(** Multi-definition typing *)
Notation "Γ ⊨ds ds : T" := (idstp p⟦Γ⟧* p⟦T⟧ ds) (at level 74, ds, T at next level).
(** Expression typing *)
Notation "Γ ⊨ e : T" := (ietp p⟦Γ⟧* p⟦T⟧ e) (at level 74, e, T at next level).
Notation "Γ ⊨p p : T , i" := (iptp p⟦Γ⟧* p⟦T⟧ p i) (at level 74, p, T, i at next level).

Notation "Γ ⊨ T1 , i <: T2 , j " := (istpi p⟦Γ⟧* p⟦T1⟧ p⟦T2⟧ i j) (at level 74, T1, T2, i, j at next level).

Section SampleTypingLemmas.
  Context `{HdotG: dlangG Σ}.

  Implicit Types (τ L T U : olty Σ 0).

  Lemma Sub_Sel Γ L U va l i:
    Γ s⊨ tv va : oTTMem l L U, i -∗
    Γ s⊨ oLater L, i <: oTSel (pv va) l, i.
  Proof.
    iIntros "#Hva !>" (ρ v) "#Hg #HvL".
    iSpecialize ("Hva" with "Hg"). rewrite /= wp_value_inv' path_wp_pv.
    iNext.
    iDestruct "Hva" as (d Hl ψ) "#[Hlψ [#HLψ #HψU]]".
    iExists ψ, d; repeat iSplit => //. by iApply "HLψ".
  Qed.

  Lemma Sel_Sub Γ L U va l i:
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

  Lemma D_Typ_Abs Γ T L U s σ l :
    Γ s⊨ T, 1 <: U, 1 -∗
    Γ s⊨ L, 1 <: T, 1 -∗
    s ↝[ σ ] T -∗
    Γ s⊨ { l := dtysem σ s } : oDTMem l L U.
  Proof.
    iIntros "#HTU #HLT #Hs /="; iSplit => //.
    iIntros "!>" (ρ) "#Hg /=".
    iDestruct "Hs" as (φ Hγφ) "Hγ".
    rewrite /dlty_car /=.
    iExists (hoEnvD_inst (σ.|[ρ]) φ); iSplit.
    by iApply dm_to_type_intro.
    iModIntro; repeat iSplit; iIntros (v) "#HL"; rewrite later_intuitionistically.
    - iIntros "!>". iApply Hγφ. by iApply "HLT".
    - iApply "HTU" => //. by iApply Hγφ.
  Qed.

  Lemma D_Typ Γ (τ : olty Σ 0) s σ l:
    s ↝[ σ ] τ -∗
    Γ s⊨ { l := dtysem σ s } : oDTMem l τ τ.
  Proof. iIntros "#Hs"; iApply D_Typ_Abs; by [| iIntros "!> **"]. Qed.
End SampleTypingLemmas.

End SemTypes.
