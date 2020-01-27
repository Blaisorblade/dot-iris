From iris.proofmode Require Import tactics.
From D Require Import iris_prelude lty.
From D.Dot Require Import syn syn.path_repl dlang_inst path_wp lr_syn_aux.
From D.pure_program_logic Require Import lifting.

Notation "'λI' x .. y , t" := (fun x => .. (fun y => t%I) ..)
  (at level 200, x binder, y binder, right associativity, only parsing,
  format "'[  ' '[  ' 'λI'  x  ..  y ']' ,  '/' t ']'") : function_scope.

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


(* Definition sdtp `{!dlangG Σ} Γ l (φ : dlty Σ) d : iProp Σ :=
  □∀ ρ, ⌜path_includes (pv (ids 0)) ρ [(l, d)] ⌝ → s⟦Γ⟧* ρ → lift_dlty φ l ρ d.|[ρ]. *)

Definition sdtp `{!dlangG Σ} Γ l (φ : dlty Σ) d : iProp Σ :=
  (⌜ l = dlty_label φ ⌝ ∧
    □∀ ρ, s⟦Γ⟧* ρ → dlty_car φ ρ d.|[ρ])%I.
Global Arguments sdtp /.
Notation "Γ s⊨ { l := d  } : T" := (sdtp Γ l T d) (at level 64, d, l, T at next level).

Definition sptp `{!dlangG Σ} Γ (τ : olty Σ 0) p i: iProp Σ :=
  □∀ ρ, s⟦Γ⟧* ρ -∗
    ▷^i path_wp (p.|[ρ]) (λ v, oClose τ ρ v).

Notation "Γ s⊨p p : τ , i" := (sptp Γ τ p i) (at level 74, p, τ, i at next level).

(*
  Even if semantic types use infinite substitutions, we can still reuse the
  current stamping theory, based on finite substitutions.
*)
Section Sec.
  Context `{HdotG: dlangG Σ} {i : nat}.
  Implicit Types (φ : hoEnvD Σ i) (τ : olty Σ i).

  Definition leadsto_envD_equiv s σ (φ : hoEnvD Σ i) : iProp Σ :=
    (∃ (φ' : hoEnvD Σ i),
      ⌜φ ≡ (λ args ρ, φ' args (∞ σ.|[ρ]))⌝ ∧ s ↝n[ i ] φ')%I.
  Arguments leadsto_envD_equiv /.

  Definition dm_to_type d i (ψ : hoD Σ i) : iProp Σ :=
    (∃ s σ, ⌜ d = dtysem σ s ⌝ ∧ s ↗n[ σ , i ] ψ)%I.
End Sec.

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
    olty0 (λ ρ v, (∃ d, ⌜v @ dlty_label T ↘ d⌝ ∧ dlty_car T ρ d)%I).

  (* Rewrite using (higher) semantic kinds! *)
  Definition oDTMem l τ1 τ2 : dlty Σ := Dlty l
    (λ ρ d,
    ∃ ψ, (d ↗n[ 0 ] ψ) ∧
       □ ((∀ v, ▷ τ1 vnil ρ v → ▷ □ ψ vnil v) ∧
          (∀ v, ▷ □ ψ vnil v → ▷ τ2 vnil ρ v)))%I.

  Definition oTTMem l τ1 τ2 :=
    lift_dinterp_vl (oDTMem l τ1 τ2).

  Definition oDVMem l τ : dlty Σ := Dlty l
    (λ ρ d, ∃ pmem, ⌜d = dpt pmem⌝ ∧ path_wp pmem (oClose τ ρ))%I.

  Definition oTVMem l τ :=
    lift_dinterp_vl (oDVMem l τ).
(*
  Program Definition oInterp T := Olty ⟦ T ⟧ _.
  Next Obligation. rewrite /vclosed=>*. by rewrite interp_vclosed. Qed. *)

  Definition oTSel p (l : label) :=
    olty0 (λ ρ v, path_wp p.|[ρ]
      (λ vp, ∃ ψ d, ⌜vp @ l ↘ d⌝ ∧ d ↗n[ 0 ] ψ ∧ ▷ □ ψ vnil v))%I.

  Definition oForall τ1 τ2 := olty0
    (λI ρ v,
    (∃ t, ⌜ v = vabs t ⌝ ∧
     □ ∀ w, ▷ τ1 vnil ρ w → ▷ interp_expr τ2 (w .: ρ) t.|[w/])).

  Lemma oTSel_pv w (l : label) args ρ v :
    oTSel (pv w) l args ρ v ≡
      (∃ ψ d, ⌜w.[ρ] @ l ↘ d⌝ ∧ d ↗n[ 0 ] ψ ∧ ▷ □ ψ vnil v)%I.
  Proof. by rewrite /= path_wp_pv. Qed.

  Definition oPSing p : olty Σ 0 :=
    olty0 (λI ρ v, ⌜alias_paths p.|[ρ] (pv v)⌝).
End SemTypes.

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
