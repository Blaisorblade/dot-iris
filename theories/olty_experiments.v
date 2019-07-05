From D Require Import iris_prelude asubst_base asubst_intf dlang.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting adequacy.
From D Require Import gen_iheap saved_interp olty dlang.

Implicit Types (Σ : gFunctors).

(*
  - Redefining *existing judgments* on Olty will let us
    generalize current typing lemmas to be about semantic types.
    + However, we need to define substitution on semantic types.
      And figure out corresponding lemmas.
      Crucially, we must have (⟦ T ⟧).|[σ] ≡ ⟦ T.|[σ] ⟧.
      We might have already proven that, for to_subst.
  - Redefining judgments will let us... do what?
    Prove theorems about judgments? What is that good for?
    - Stating the lemmas without mentioning Γ?
    - Using common notation [Γ ⊨ J] for judgments?
    Neither seems so compelling.
  - What would be useful would be to prepare for HK-D<:
    while reusing as much as possible.
*)

Module Type OLty_judge (Import VS: VlSortsFullSig).

Include OLty VS.

Class Closeable s := nclosed_s : s → nat → Prop.
Instance closeable_sort s `{Sort s} : Closeable s := nclosed.
Instance closeable_vl : Closeable vl := nclosed_vl.

Definition env := var -> vl.

Implicit Types (v: vl) (vs : vls) (ρ : env).

Section judgments.
Context `{dlangG Σ} `{OTyInterp ty Σ}.
Implicit Type (τ : olty Σ).

Notation ctx := (list ty).

Notation "⟦ T ⟧" := (oty_interp T).

Definition oty_interp_env (Γ : ctx) : sCtx := map oty_interp Γ.
Definition env_typed (Γ : ctx) : vls -d> iProp Σ := env_oltyped_fin (oty_interp_env Γ).

Global Instance env_typed_persistent' `{OTyInterp ty Σ} Γ vs : Persistent (env_typed Γ vs) := env_oltyped_fin_persistent _ _.

Definition judgment Σ s : Type := option s * (env -d> option s -d> iProp Σ).
Definition nosubj_judgment Σ : Type := env -d> iProp Σ.
Definition subj_judgment Σ s : Type := s * (env -d> s -d> iProp Σ).
Program Definition subj_judgment_to_judgment {Σ s} : subj_judgment Σ s → judgment Σ s :=
  λ '(x, φ), (Some x, λ ρ, from_option (φ ρ) False)%I.

Definition judgment_holds `{Closeable s} (Γ : sCtx) (J : judgment Σ s): iProp Σ :=
  (⌜ from_option (flip nclosed_s (length Γ)) True (fst J) ⌝ ∗ □∀ vs, env_oltyped_fin Γ vs → (snd J) (to_subst vs) (fst J))%I.
Notation "Γ ⊨ J" := (judgment_holds Γ J) (at level 74, J at next level).
Global Arguments judgment_holds /.

Program Definition ivtp τ v : judgment Σ vl := subj_judgment_to_judgment (v, τ).
Global Arguments ivtp /.

(* DOT/D<: judgments are indexed by [⋅]. *)
Notation "v v⋅: τ" := (ivtp τ v) (at level 73).
Local Definition test_judge_me Γ v τ := Γ ⊨ v v⋅: τ.

Context `{Closeable tm}.
Definition ittp τ t : judgment Σ tm := subj_judgment_to_judgment (t, interp_expr τ).
Global Arguments ittp /.

(* DOT/D<: judgments are indexed by [⋅]. *)
Notation "t t⋅: τ" := (ittp τ t) (at level 73).
Definition test_judge_me2 Γ t τ := Γ ⊨ t t⋅: τ.
(* Choosing vl is arbitrary. *)
Program Definition nosubj_judgment_to_judgment {Σ} : nosubj_judgment Σ → judgment Σ vl :=
  λ φ, (None, λ ρ _, φ ρ).

Definition ivstp τ1 τ2 : nosubj_judgment Σ := (λ ρ, ∀ v, ⌜ nclosed_vl v 0 ⌝ → τ1 ρ v → τ2 ρ v)%I.
Program Definition step_indexed_ivstp τ1 i1 τ2 i2 := nosubj_judgment_to_judgment (Σ := Σ)
  (λ ρ, ∀ v, ⌜ nclosed_vl v 0 ⌝ → (▷^i1 τ1 ρ v) → ▷^i2 τ2 ρ v)%I.
Notation "[ τ1 , i1 ] <: [ τ2 , i2 ]" := (step_indexed_ivstp τ1 i1 τ2 i2) (at level 73).

Lemma equiv_vstp Γ τ1 τ2 i1 i2: Γ ⊨ [τ1 , i1] <: [τ2 , i2] ⊣⊢
    (□∀ vs v, ⌜ nclosed_vl v 0 ⌝ → env_oltyped_fin Γ vs → (▷^i1 τ1 (to_subst vs) v) → ▷^i2 τ2 (to_subst vs) v)%I.
Proof.
  iSplit; [iIntros "#[_ H] /= !>" (???) "#?" |
    iIntros "#H"; iSplit; first done; iIntros "!>" (?) "#? /="; iIntros (??)].
  all: by iApply "H".
Qed.

Lemma andstp1 Γ τ1 τ2 i : Γ ⊨ [oAnd τ1 τ2 , i] <: [τ1 , i].
Proof.
  rewrite equiv_vstp /=. by iIntros "!>" (???) "#Hg #[? ?]".
Qed.
End judgments.

End OLty_judge.

From D.Dot Require Import syn synLemmas rules typeExtractionSyn path_wp.

Implicit Types
         (v: vl) (e: tm) (d: dm) (ds: dms) (p : path).

Module SemTypes.

Include OLtyJudgements VlSorts.

Record dlty Σ := Dlty {
  dlty_label : label;
  dlty_car : ((var → vl) -d> dm -d> iProp Σ);
  dlty_persistent ρ d :> Persistent (dlty_car ρ d);
}.
Global Arguments Dlty {_} _%I _ {_}.
Global Arguments dlty_car {_} _ _ _ : simpl never.
Global Arguments dlty_label {_} _ /.
Global Existing Instance dlty_persistent.

Definition idtp `{dlangG Σ} Γ l (φ : dlty Σ) d : iProp Σ :=
  (⌜ nclosed d (length Γ) ⌝ ∧ ⌜ l = dlty_label φ ⌝ ∗
    □∀ ρ, ⟦Γ⟧* ρ → dlty_car φ (to_subst ρ) d.|[to_subst ρ])%I.
Global Arguments idtp /.
Notation "Γ ⊨d{ l := d  } : T" := (idtp Γ l T d) (at level 64, d, l, T at next level).

Section SemTypes.
  Context `{HdotG: dlangG Σ}.

  Implicit Types (φ : envD Σ) (τ : olty Σ) (ψ : vl → iProp Σ).

  Program Definition lift_dinterp_vl (T : dlty Σ): olty Σ :=
    closed_olty (λ ρ v, (∃ d, ⌜v @ dlty_label T ↘ d⌝ ∧ dlty_car T ρ d)%I).

  Definition dm_to_type d ψ : iProp Σ :=
    (∃ s σ interp, ⌜ d = dtysem σ s ∧ ψ = interp (to_subst σ) ⌝ ∗ s ↝ interp)%I.
  Notation "d ↗ ψ" := (dm_to_type d ψ) (at level 20).
  Global Instance dm_to_type_persistent d ψ: Persistent (d ↗ ψ) := _.

  Lemma dm_to_type_agree d ψ1 ψ2 v :
    d ↗ ψ1 -∗ d ↗ ψ2 -∗ ▷ (ψ1 v ≡ ψ2 v).
  Proof.
    iIntros "/= #Hd1 #Hd2".
    iDestruct "Hd2" as (s' σ' interp2 ?) "Hs2".
    iDestruct "Hd1" as (s σ interp1 ?) "Hs1".
    ev; simplify_eq. by iApply (leadsto_agree _ interp1 interp2).
  Qed.

  Lemma dm_to_type_intro s σ φ :
    s ↝ φ -∗ dtysem σ s ↗ φ (to_subst σ).
  Proof. iIntros. iExists s, σ , φ. by iSplit. Qed.

  Global Opaque dm_to_type.

  Definition oDTMem l τ1 τ2 : dlty Σ := Dlty l
    (λ ρ d,
    ∃ ψ, (d ↗ ψ) ∗
       □ ((∀ v, ⌜ nclosed_vl v 0 ⌝ → ▷ τ1 ρ v → ▷ □ ψ v) ∗
          (∀ v, ⌜ nclosed_vl v 0 ⌝ → ▷ □ ψ v → ▷ τ2 ρ v)))%I.

  Definition oTTMem l τ1 τ2 :=
    lift_dinterp_vl (oDTMem l τ1 τ2).

  Definition oDVMem l τ : dlty Σ := Dlty l
    (λ ρ d, ∃ vmem, ⌜d = dvl vmem⌝ ∧ ▷ τ ρ vmem)%I.

  Definition oTVMem l τ :=
    lift_dinterp_vl (oDVMem l τ).
(*
  Program Definition oInterp T := Olty ⟦ T ⟧ _.
  Next Obligation. rewrite /vclosed=>*. by rewrite interp_vclosed. Qed. *)

  Definition oTSel p (l : label) :=
    closed_olty (λ ρ v, path_wp p.|[ρ]
      (λ vp, ∃ ψ d, ⌜vp @ l ↘ d⌝ ∧ d ↗ ψ ∧ ▷ □ ψ v)%I).

  Lemma Sub_Sel Γ L U va l i:
    Γ ⊨ tv va : oTTMem l L U, i -∗
    Γ ⊨ [oLater L, i] <: [oTSel (pv va) l, i].
  Proof.
    iIntros "#[% #Hva] !>" (ρ v Hclv) "#Hg #[_ HvL]". iFrame (Hclv).
    iSpecialize ("Hva" with "Hg"). rewrite /= wp_value_inv'.
    iNext.
    iDestruct "Hva" as (Hclvas' d Hl ψ) "#[Hlψ [#HLψ #HψU]]".
    iExists ψ, d; repeat iSplit => //. by iApply "HLψ".
  Qed.

  Lemma Sel_Sub Γ L U va l i:
    Γ ⊨ tv va : oTTMem l L U, i -∗
    Γ ⊨ [oTSel (pv va) l, i] <: [oLater U, i].
  Proof.
    iIntros "#[% #Hva] !>" (ρ v Hclv) "#Hg [$ #Hψ]". move: H => Hclva.
    iSpecialize ("Hva" with "Hg"); rewrite /= wp_value_inv'.
    iNext.
    iDestruct "Hva" as (Hclvas d Hl ψ) "#[Hlψ [#HLψ #HψU]]".
    iDestruct "Hψ" as (ψ1 d1 Hva) "[Hγ #Hψ1v]".
    objLookupDet; subst. iDestruct (dm_to_type_agree d _ _ v with "Hlψ Hγ") as "#Hag".
    iApply "HψU" => //. iNext. by iRewrite "Hag".
  Qed.

(*
  (* Alternative (and failed) definition. *)
  Program Definition sem_sel p (l : label) :=
    closed_olty (λ ρ v, path_wp p.|[ρ]
      (λ vp, ∃ ψ d, ⌜vp @ l ↘ d⌝ ∧ d ↗ ψ ∧ □ ψ v)%I).

  Lemma Sub_Sel2 Γ L U va l i:
    Γ ⊨ tv va : oTTMem l L U, i -∗
    Γ ⊨ [oLater L, i] <: [oLater (sem_sel (pv va) l), i].
  Proof.
    iIntros "/= #[% #Hva] !>" (ρ v Hclv) "#Hg #[_ HvL]". move: H => Hclva. iFrame (Hclv).
    iSpecialize ("Hva" with "Hg"); rewrite wp_value_inv'.
    iNext.

    iDestruct "Hva" as (Hclvas' d Hl ψ) "#[Hlψ [#HLψ ?]]".
    iSpecialize ("HLψ" $! _ Hclv with "HvL").
    rewrite -later_intuitionistically.
    iExists ψ, d; by repeat iSplit.
  Qed.

  Lemma Sel_Sub2_Failed Γ L U va l i:
    Γ ⊨ tv va : oTTMem l L U, i -∗
    Γ ⊨ [oLater ((sem_sel (pv va) l)), i] <: [oLater U, i].
  Proof.
    iIntros "/= #[% #Hva] !>" (ρ v Hclv) "#Hg #[$ #[_ Hψ]]".
    iSpecialize ("Hva" with "Hg"); rewrite wp_value_inv'.
    iNext.
    iDestruct "Hva" as (Hclvas d Hl ψ) "#[Hlψ [_ #HψU]]".
    iApply "HψU" => //.
    rewrite -later_intuitionistically.
    iDestruct "Hψ" as (ψ1 d1) "[>% [Hγ #Hψ1v]]".
    (* iSpecialize ("HLψ" $! v Hclv); iSpecialize ("HψU" $! v Hclv). *)
    (* rewrite /sem_sel /olty_car. *)
    objLookupDet; subst. iNext. iDestruct (dm_to_type_agree d _ _ v with "Hlψ Hγ") as "#Hag".
    repeat iModIntro. Fail by iRewrite "Hag".
  Abort. *)
End SemTypes.

(*
  Even if semantic types use infinite substitutions, we can still reuse the
  current stamping theory, based on finite substitutions.
*)
Module FinSubst.
Section Sec.
  Context `{HdotG: dlangG Σ}.
  Implicit Types (φ : envD Σ) (τ : olty Σ).

  Definition envD_equiv n φ1 φ2 : iProp Σ :=
    (∀ ρ v, ⌜ length ρ = n ⌝ → ⌜ cl_ρ ρ ⌝ → φ1 (to_subst ρ) v ≡ φ2 (to_subst ρ) v)%I.
  Notation "φ1 ≈[  n  ] φ2" := (envD_equiv n φ1 φ2) (at level 70).

  Definition leadsto_envD_equiv (sσ : extractedTy) n φ : iProp Σ :=
    let '(s, σ) := sσ in
    (⌜nclosed_σ σ n⌝ ∧ ∃ (φ' : envD Σ), s ↝ φ' ∗ envD_equiv n φ (λ ρ, φ' (to_subst σ.|[ρ])))%I.
  Arguments leadsto_envD_equiv /.
  Notation "sσ ↝[  n  ] φ" := (leadsto_envD_equiv sσ n φ) (at level 20).

  Lemma D_Typ Γ T L U s σ l :
    Γ ⊨ [T, 1] <: [U, 1] -∗
    Γ ⊨ [L, 1] <: [T, 1] -∗
    (s, σ) ↝[ length Γ ] T -∗
    Γ ⊨d{ l := dtysem σ s } : oDTMem l L U.
  Proof.
    iIntros "#HTU #HLT #[% Hs] /="; repeat iSplit; [auto using fv_dtysem..|].
    iIntros "!>" (ρ) "#Hg /=".
    iDestruct (interp_env_props with "Hg") as %[Hclp Hlen]; rewrite <- Hlen in *.
    (* iDestruct (env_oltyped_fin_cl_ρ with "Hg") as %Hclp. *)
    iDestruct "Hs" as (φ) "[Hγ Hγφ]".
    iExists (φ (to_subst σ.|[to_subst ρ])); iSplit.
    by iApply dm_to_type_intro.
    rewrite /envD_equiv.
    iModIntro; repeat iSplitL; iIntros (v Hclv) "#HL"; rewrite later_intuitionistically.
    - iIntros "!>". iApply (internal_eq_iff with "(Hγφ [#//] [#//])").
      by iApply "HLT".
    - iApply "HTU" => //.
      by iApply (internal_eq_iff with "(Hγφ [#//] [#//])").
  Qed.

  Lemma D_Typ_Concr Γ τ s σ l:
    (s, σ) ↝[ length Γ ] τ -∗
    Γ ⊨d{ l := dtysem σ s } : oDTMem l τ τ.
  Proof. iIntros "#Hs"; iApply D_Typ; by [| iIntros "!> **"]. Qed.
End Sec.
End FinSubst.

Module InfSubst.
Section Sec.
  Context `{HdotG: dlangG Σ}.
  Implicit Types (φ : envD Σ) (τ : olty Σ).

  Definition infEnvD_equiv n φ1 φ2 : iProp Σ :=
    (∀ ρ v, ⌜ nclosed_sub n 0 ρ ⌝ → φ1 ρ v ≡ φ2 ρ v)%I.
  Notation "φ1 ≈[  n  ] φ2" := (infEnvD_equiv n φ1 φ2) (at level 70).

  Definition leadsto_infEnvD_equiv (sσ: extractedTy) n φ : iProp Σ :=
    let '(s, σ) := sσ in
    (⌜nclosed_σ σ n⌝ ∧ ∃ (φ' : envD Σ), s ↝ φ' ∗
      infEnvD_equiv n φ (λ ρ, φ' (to_subst σ.|[ρ])))%I.
  Notation "sσ ↝[  n  ] φ" := (leadsto_infEnvD_equiv sσ n φ) (at level 20).

  Lemma D_Typ Γ T L U s σ l :
    Γ ⊨ [T, 1] <: [U, 1] -∗
    Γ ⊨ [L, 1] <: [T, 1] -∗
    (s, σ) ↝[ length Γ ] T -∗
    Γ ⊨d{ l := dtysem σ s } : oDTMem l L U.
  Proof.
    iIntros "#HTU #HLT #[% Hs] /="; repeat iSplit; [auto using fv_dtysem..|].
    iIntros "!>" (ρ) "#Hg /=".
    iDestruct (env_oltyped_fin_cl_ρ with "Hg") as %Hclp.
    iDestruct "Hs" as (φ) "[Hγ Hγφ]".
    iExists (φ (to_subst σ.|[to_subst ρ])); iSplit.
    by iApply dm_to_type_intro.
    iModIntro; repeat iSplitL; iIntros (v Hclv) "#HL"; rewrite later_intuitionistically.
    - iIntros "!>". iApply (internal_eq_iff with "(Hγφ [#//])").
      by iApply "HLT".
    - iApply "HTU" => //.
      by iApply (internal_eq_iff with "(Hγφ [#//])").
  Qed.

  Lemma D_Typ_Concr Γ τ s σ l:
    (s, σ) ↝[ length Γ ] τ -∗
    Γ ⊨d{ l := dtysem σ s } : oDTMem l τ τ.
  Proof. iIntros "#Hs"; iApply D_Typ; by [| iIntros "!> **"]. Qed.
End Sec.
End InfSubst.

End SemTypes.
