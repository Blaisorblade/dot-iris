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

Module Type OLty_judge (Import vals: Values) (Import sorts: SortsLemmas vals).
(* TODO Eventually switch to: *)

(* Or just inline this code there. *)
Include OLty vals sorts.

Class Closeable s := nclosed_s : s → nat → Prop.
Instance closeable_sort s `{Sort s} : Closeable s := nclosed.
Instance closeable_vl : Closeable vl := nclosed_vl.

Definition env := var -> vl.

Implicit Types (v: vl) (vs : vls) (ρ : env).

Definition test_interp_expr2 `{dlangG Σ} (φ : olty Σ) :=
  λ ρ t, WP t {{ φ ρ }} %I.

Section judgments.
Context `{dlangG Σ} `{OTyInterp ty Σ}.
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

Program Definition ivtp (φ : olty Σ) v : judgment Σ vl := subj_judgment_to_judgment (v, φ).
Global Arguments ivtp /.

(* DOT/D<: judgments are indexed by [⋅]. *)
Notation "v v⋅: φ" := (ivtp φ v) (at level 73).
Definition judge_me Γ v φ := Γ ⊨ v v⋅: φ.

Definition interp_expr (φ : olty Σ) :=
  λ ρ t, WP t {{ φ ρ }} %I.
Global Arguments interp_expr /.
Definition tm := expr dlang_lang.
Context `{Closeable tm}.
Definition ittp (φ: olty Σ) t : judgment Σ tm := subj_judgment_to_judgment (t, interp_expr φ).
Global Arguments ittp /.

(* DOT/D<: judgments are indexed by [⋅]. *)
Notation "t t⋅: φ" := (ittp φ t) (at level 73).
Definition judge_me2 Γ t φ := Γ ⊨ t t⋅: φ.
(* Choosing vl is arbitrary. *)
Program Definition nosubj_judgment_to_judgment {Σ} : nosubj_judgment Σ → judgment Σ vl :=
  λ φ, (None, λ ρ _, φ ρ)%I.
Implicit Type (φ: olty Σ).

Definition ivstp φ1 φ2 : nosubj_judgment Σ := (λ ρ, ∀ v, ⌜ nclosed_vl v 0 ⌝ → φ1 ρ v → φ2 ρ v)%I.
Program Definition step_indexed_ivstp φ1 i1 φ2 i2 := nosubj_judgment_to_judgment (Σ := Σ)
  (λ ρ, ∀ v, ⌜ nclosed_vl v 0 ⌝ → (▷^i1 φ1 ρ v) → ▷^i2 φ2 ρ v)%I.
Notation "[ φ1 , i1 ] <: [ φ2 , i2 ]" := (step_indexed_ivstp φ1 i1 φ2 i2) (at level 73).
Lemma equiv_vstp Γ (φ1 φ2: olty Σ) i1 i2: (Γ ⊨ [φ1 , i1] <: [φ2 , i2]) ⊣⊢
    (□∀ vs v, ⌜ nclosed_vl v 0 ⌝ → env_oltyped_fin Γ vs → (▷^i1 φ1 (to_subst vs) v) → ▷^i2 φ2 (to_subst vs) v)%I.
Proof.
  iSplit; [iIntros "#[_ H] /= !>" (???) "#?" |
    iIntros "#H"; iSplit; first done; iIntros "!>" (?) "#? /="; iIntros (??)].
  all: by iApply "H".
Qed.
Program Definition oAnd φ1 φ2 : olty Σ := Olty (λ ρ v, φ1 ρ v ∧ φ2 ρ v)%I _.
Next Obligation. rewrite /vclosed; intros; iIntros "#[H _]". by iApply olty_v_closed. Qed.

Program Definition oOr φ1 φ2 : olty Σ := Olty (λ ρ v, φ1 ρ v ∨ φ2 ρ v)%I _.
Next Obligation. rewrite /vclosed; intros; iIntros "#[H | H]"; by iApply olty_v_closed. Qed.

Lemma andstp1 Γ φ1 φ2 i : (Γ ⊨ [oAnd φ1 φ2 , i] <: [φ1 , i]).
Proof.
  rewrite equiv_vstp /=. by iIntros "!>" (???) "#Hg #[? ?]".
Qed.
End judgments.

End OLty_judge.

From D.Dot Require Import syn synLemmas rules typeExtractionSyn path_wp.

Implicit Types
         (v: vl) (e: tm) (d: dm) (ds: dms) (p : path).

Module SemTypes.

Include OLty syn syn.

Set Primitive Projections.
Record dlty Σ := Dlty {
  dlty_label : label;
  dlty_car : ((var → vl) -d> dm -d> iProp Σ);
  dlty_persistent ρ d :> Persistent (dlty_car ρ d);
}.
Global Arguments Dlty {_} _%I _ {_}.
Global Arguments dlty_car {_} _ _ _ /.
Global Arguments dlty_label {_} _ /.
Global Existing Instance dlty_persistent.

Section Judgments.
  Context `{HdotG: dlangG Σ}.

  Implicit Types (φ : olty Σ).

  Definition interp_expr (φ : envD Σ) :=
    λ ρ t, WP t {{ φ ρ }} %I.
  Global Arguments interp_expr /.

  Definition ietp Γ φ e : iProp Σ := (⌜ nclosed e (length Γ) ⌝ ∗
    □∀ ρ, ⟦Γ⟧* ρ → interp_expr φ (to_subst ρ) (e.|[to_subst ρ]))%I.
  Global Arguments ietp /.

  Definition step_indexed_ietp Γ φ e i: iProp Σ :=
    (⌜ nclosed e (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ →
      interp_expr (λ ρ v, ▷^i φ ρ v) (to_subst ρ) (e.|[to_subst ρ]))%I.
  Global Arguments step_indexed_ietp /.

  Definition step_indexed_ivstp Γ φ1 φ2 i j: iProp Σ :=
    (□∀ ρ v, ⌜ nclosed_vl v 0 ⌝ →
      ⟦Γ⟧*ρ → (▷^i φ1 (to_subst ρ) v) → ▷^j φ2 (to_subst ρ) v)%I.
  Global Arguments step_indexed_ivstp /.

  Definition idtp Γ l (T : dlty Σ) d : iProp Σ :=
    (⌜ nclosed d (length Γ) ⌝ ∧ ⌜ l = dlty_label T ⌝ ∗
      □∀ ρ, ⟦Γ⟧* ρ → dlty_car T (to_subst ρ) d.|[to_subst ρ])%I.

  Global Arguments idtp /.
End Judgments.

Notation "Γ ⊨ e : φ" := (ietp Γ φ e) (at level 74, e, φ at next level).
Notation "Γ ⊨ e : T , i" := (step_indexed_ietp Γ T e i) (at level 74, e, T at next level).
Notation "Γ ⊨ [ φ1 , i ]  <: [ φ2 , j ]" := (step_indexed_ivstp Γ φ1 φ2 i j) (at level 74, φ1, φ2 at next level): bi_scope.
Notation "Γ ⊨d{ l := d  } : T" := (idtp Γ l T d) (at level 64, d, l, T at next level).

Section SemTypes.
  Context `{HdotG: dlangG Σ}.

  Implicit Types (φ : olty Σ) (τ : vl → iProp Σ).

  Program Definition closed_olty (φ : envD Σ) `{∀ ρ v, Persistent (φ ρ v)} : olty Σ :=
    Olty (λ ρ v, ⌜ nclosed_vl v 0 ⌝ ∗ φ ρ v)%I _.
  Next Obligation. iIntros (????) "[$_]". Qed.

  Program Definition lift_dinterp_vl (T : dlty Σ): olty Σ :=
    closed_olty (λ ρ v, (∃ d, ⌜v @ dlty_label T ↘ d⌝ ∧ dlty_car T ρ d)%I).

  Definition oLater φ :=
    closed_olty (λ ρ v, ▷ φ ρ v)%I.

  Lemma interp_env_lookup Γ ρ φ x:
    Γ !! x = Some φ →
    ⟦ Γ ⟧* ρ -∗ φ.|[ren (+x)] (to_subst ρ) (to_subst ρ x).
  Proof.
    elim: Γ x ρ => [//|φ' Γ' IHΓ] [//|x] [//|v ρ] /= Hx;
      try by [|iIntros "[]"]; iDestruct 1 as "[Hg Hv]".
    - move: Hx => [ -> ]. by locAsimpl.
    - iApply (olty_weaken_one v (φ.|[ren (+x)])).
      iApply (IHΓ x ρ Hx with "Hg").
  Qed.

  Lemma T_Var Γ x φ:
    Γ !! x = Some φ →
    (*──────────────────────*)
    Γ ⊨ tv (ids x) : φ.|[ren (+x)].
  Proof.
    iIntros (Hx) "/=". iSplit. eauto using lookup_fv.
    iIntros "!> * #Hg". rewrite -wp_value' interp_env_lookup; by [].
  Qed.

  Lemma iterate_TLater_later i (φ : olty Σ) ρ v:
    nclosed_vl v 0 →
    (iterate oLater i φ) ρ v ≡ (▷^i φ ρ v)%I.
  Proof.
    elim: i => [|i IHi] // => Hcl. rewrite iterate_S /= IHi //.
    iSplit; by [iIntros "#[_ $]" | iIntros "$"].
  Qed.

  Definition idm_proj_semtype d τ : iProp Σ :=
    (∃ s σ interp, ⌜ d = dtysem σ s ∧ τ = interp (to_subst σ) ⌝ ∗ s ↝ interp)%I.
  Notation "d ↗ τ" := (idm_proj_semtype d τ) (at level 20).
  Global Instance idm_proj_persistent d τ: Persistent (d ↗ τ) := _.

  Lemma stored_pred_agree d τ1 τ2 v :
    d ↗ τ1 -∗ d ↗ τ2 -∗ ▷ (τ1 v ≡ τ2 v).
  Proof.
    iIntros "/= #Hd1 #Hd2".
    iDestruct "Hd2" as (s' σ' interp2 ?) "Hs2".
    iDestruct "Hd1" as (s σ interp1 ?) "Hs1".
    ev; simplify_eq. by iApply (leadsto_agree _ interp1 interp2).
  Qed.

  Lemma idm_proj_intro s σ (φ : envD Σ) :
    s ↝ φ -∗ dtysem σ s ↗ φ (to_subst σ).
  Proof. iIntros. iExists s, σ , φ. by iSplit. Qed.

  Global Opaque idm_proj_semtype.

  Definition oDTMem l φ1 φ2 : dlty Σ := Dlty l
    (λ ρ d,
    ∃ τ, (d ↗ τ) ∗
       □ ((∀ v, ⌜ nclosed_vl v 0 ⌝ → ▷ φ1 ρ v → □ ▷ τ v) ∗
          (∀ v, ⌜ nclosed_vl v 0 ⌝ → □ ▷ τ v → ▷ φ2 ρ v)))%I.

  Definition oTTMem l φ1 φ2 :=
    lift_dinterp_vl (oDTMem l φ1 φ2).

  Definition oDVMem l φ : dlty Σ := Dlty l
    (λ ρ d, ∃ vmem, ⌜d = dvl vmem⌝ ∧ ▷ φ ρ vmem)%I.

  Definition oTVMem l φ :=
    lift_dinterp_vl (oDVMem l φ).
(*
  Program Definition oInterp T := Olty ⟦ T ⟧ _.
  Next Obligation. rewrite /vclosed=>*. by rewrite interp_v_closed. Qed. *)

  Definition oTSel p (l : label) :=
    closed_olty (λ ρ v, path_wp p.|[ρ]
      (λ vp, ∃ ϕ d, ⌜vp @ l ↘ d⌝ ∧ d ↗ ϕ ∧ □ ▷ ϕ v)%I).

  Lemma Sub_Sel Γ L U va l i:
    Γ ⊨ tv va : oTTMem l L U, i -∗
    Γ ⊨ [oLater L, i] <: [oTSel (pv va) l, i].
  Proof.
    iIntros "#[% #Hva] !>" (ρ v Hclv) "#Hg #[_ HvL]". iFrame (Hclv).
    iSpecialize ("Hva" with "Hg"). rewrite /= wp_value_inv'.
    iNext.
    iDestruct "Hva" as (Hclvas' d Hl φ) "#[Hlφ [#HLφ #HφU]]".
    iExists φ, d; repeat iSplit => //. by iApply "HLφ".
  Qed.

  Lemma Sel_Sub Γ L U va l i:
    Γ ⊨ tv va : oTTMem l L U, i -∗
    Γ ⊨ [oTSel (pv va) l, i] <: [oLater U, i].
  Proof.
    iIntros "#[% #Hva] !>" (ρ v Hclv) "#Hg [$ #Hφ]". move: H => Hclva.
    iSpecialize ("Hva" with "Hg"); rewrite /= wp_value_inv'.
    iNext.
    iDestruct "Hva" as (Hclvas d Hl φ) "#[Hlφ [#HLφ #HφU]]".
    iDestruct "Hφ" as (φ1 d1 Hva) "[Hγ #HΦ1v]".
    objLookupDet; subst. iDestruct (stored_pred_agree d _ _ v with "Hlφ Hγ") as "#Hag".
    iApply "HφU" => //. iModIntro. iNext. by iRewrite "Hag".
  Qed.

(*
  (* Alternative (and failed) definition. *)
  Program Definition sem_sel p (l : label) :=
    closed_olty (λ ρ v, path_wp p.|[ρ]
      (λ vp, ∃ ϕ d, ⌜vp @ l ↘ d⌝ ∧ d ↗ ϕ ∧ □ ϕ v)%I).

  Lemma Sub_Sel2 Γ L U va l i:
    Γ ⊨ tv va : oTTMem l L U, i -∗
    Γ ⊨ [oLater L, i] <: [oLater (sem_sel (pv va) l), i].
  Proof.
    iIntros "/= #[% #Hva] !>" (ρ v Hclv) "#Hg #[_ HvL]". move: H => Hclva. iFrame (Hclv).
    iSpecialize ("Hva" with "Hg"); rewrite wp_value_inv'.
    iNext.

    iDestruct "Hva" as (Hclvas' d Hl φ) "#[Hlφ [#HLφ ?]]".
    iSpecialize ("HLφ" $! _ Hclv with "HvL").
    rewrite -later_intuitionistically.
    iExists φ, d; by repeat iSplit.
  Qed.

  Lemma Sel_Sub2_Failed Γ L U va l i:
    Γ ⊨ tv va : oTTMem l L U, i -∗
    Γ ⊨ [oLater ((sem_sel (pv va) l)), i] <: [oLater U, i].
  Proof.
    iIntros "/= #[% #Hva] !>" (ρ v Hclv) "#Hg #[$ #[_ Hφ]]".
    iSpecialize ("Hva" with "Hg"); rewrite wp_value_inv'.
    iNext.
    iDestruct "Hva" as (Hclvas d Hl φ) "#[Hlφ [_ #HφU]]".
    iApply "HφU" => //.
    rewrite -later_intuitionistically.
    iDestruct "Hφ" as (φ1 d1) "[>% [Hγ #HΦ1v]]".
    (* iSpecialize ("HLφ" $! v Hclv); iSpecialize ("HφU" $! v Hclv). *)
    (* rewrite /sem_sel /olty_car. *)
    objLookupDet; subst. iNext. iDestruct (stored_pred_agree d _ _ v with "Hlφ Hγ") as "#Hag".
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
  Implicit Types (φ: olty Σ) (τ : vl → iProp Σ).

  Definition envD_equiv n (φ1 φ2 : envD Σ): iProp Σ :=
    (∀ ρ v, ⌜ length ρ = n ⌝ → ⌜ cl_ρ ρ ⌝ → φ1 (to_subst ρ) v ≡ φ2 (to_subst ρ) v)%I.
  Notation "φ1 ≈[  n  ] φ2" := (envD_equiv n φ1 φ2) (at level 70).

  Definition leadsto_envD_equiv (sσ : extractedTy) n (φ : envD Σ) : iProp Σ :=
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
    by iApply idm_proj_intro.
    rewrite /envD_equiv.
    iModIntro; repeat iSplitL; iIntros (v Hclv) "#HL".
    - iIntros "!>". iApply (internal_eq_iff with "(Hγφ [#//] [#//])").
      by iApply "HLT".
    - iApply "HTU" => //.
      by iApply (internal_eq_iff with "(Hγφ [#//] [#//])").
  Qed.

  Lemma D_Typ_Concr Γ φ s σ l:
    (s, σ) ↝[ length Γ ] φ -∗
    Γ ⊨d{ l := dtysem σ s } : oDTMem l φ φ.
  Proof. iIntros "#Hs"; iApply D_Typ; by [| iIntros "!> **"]. Qed.
End Sec.
End FinSubst.

Module InfSubst.
Section Sec.
  Context `{HdotG: dlangG Σ}.
  Implicit Types (φ: olty Σ) (τ : vl → iProp Σ).

  Definition infEnvD_equiv n (φ1 φ2 : envD Σ) : iProp Σ :=
    (∀ ρ v, ⌜ nclosed_sub n 0 ρ ⌝ → φ1 ρ v ≡ φ2 ρ v)%I.
  Notation "φ1 ≈[  n  ] φ2" := (infEnvD_equiv n φ1 φ2) (at level 70).

  Definition leadsto_infEnvD_equiv (sσ: extractedTy) n (φ : envD Σ) : iProp Σ :=
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
    by iApply idm_proj_intro.
    iModIntro; repeat iSplitL; iIntros (v Hclv) "#HL".
    - iIntros "!>". iApply (internal_eq_iff with "(Hγφ [#//])").
      by iApply "HLT".
    - iApply "HTU" => //.
      by iApply (internal_eq_iff with "(Hγφ [#//])").
  Qed.

  Lemma D_Typ_Concr Γ φ s σ l:
    (s, σ) ↝[ length Γ ] φ -∗
    Γ ⊨d{ l := dtysem σ s } : oDTMem l φ φ.
  Proof. iIntros "#Hs"; iApply D_Typ; by [| iIntros "!> **"]. Qed.
End Sec.
End InfSubst.

End SemTypes.
