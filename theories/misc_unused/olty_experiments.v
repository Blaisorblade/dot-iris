From D Require Import iris_prelude asubst_base asubst_intf dlang.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting adequacy.
From D Require Import gen_iheap saved_interp lty dlang.

Implicit Types (Σ : gFunctors).

(*
  - Redefining *existing judgments* on Lty will let us
    generalize current typing lemmas to be about semantic types.
    + However, we need to define substitution on semantic types.
      And figure out corresponding lemmas.
      Crucially, we must have ⟦ T ⟧.|[σ] ≡ ⟦ T.|[σ] ⟧.
      We might have already proven that, for ∞.
  - Redefining judgments will let us... do what?
    Prove theorems about judgments? What is that good for?
    - Stating the lemmas without mentioning Γ?
    - Using common notation [Γ ⊨ J] for judgments?
    Neither seems so compelling.
  - What would be useful would be to prepare for HK-D<:
    while reusing as much as possible.
*)

Module Type Lty_judge (Import VS: VlSortsFullSig) (Import LVS : LiftWp VS).
Include Lty VS LVS.

Implicit Types (v: vl) (vs : vls) (ρ : env).

Section judgments.
Context `{dlangG Σ} `{OTyInterp ty Σ}.
Implicit Type (τ : olty Σ 0).

Notation ctx := (list (ty 0)).

Notation "⟦ T ⟧" := (oty_interp T).

Definition oty_interp_env (Γ : ctx) : sCtx Σ := map oty_interp Γ.
Definition env_typed (Γ : ctx) : env -d> iPropO Σ := env_oltyped (oty_interp_env Γ).

Global Instance env_typed_persistent' `{OTyInterp ty Σ} Γ ρ : Persistent (env_typed Γ ρ) :=
  env_oltyped_persistent _ _.

Definition judgment Σ : Type := env -d> iPropO Σ.
Definition nosubj_judgment Σ : Type := env -d> iPropO Σ.
Definition subj_judgment Σ s : Type := s * (env -d> s -d> iPropO Σ).
Program Definition subj_judgment_to_judgment {Σ s} : subj_judgment Σ s → judgment Σ :=
  λ '(x, φ) ρ, φ ρ x.

Definition judgment_holds (Γ : sCtx Σ) (J : judgment Σ): iProp Σ :=
  □∀ ρ, env_oltyped Γ ρ → J ρ.
Notation "Γ ⊨ J" := (judgment_holds Γ J) (at level 74, J at next level).
Global Arguments judgment_holds /.

Program Definition ivtp τ v : judgment Σ := subj_judgment_to_judgment (v, oClose τ).
Global Arguments ivtp /.

(* DOT/D<: judgments are indexed by [⋅]. *)
Notation "v v⋅: τ" := (ivtp τ v) (at level 73).
Local Definition test_judge_me Γ v τ := Γ ⊨ v v⋅: τ.

Definition ietp τ t : judgment Σ := subj_judgment_to_judgment (t, interp_expr τ).
Global Arguments ietp /.

(* DOT/D<: judgments are indexed by [⋅]. *)
Notation "t ⋅: τ" := (ietp τ t) (at level 73).
Definition test_judge_me2 Γ t τ := Γ ⊨ t ⋅: τ.
Program Definition nosubj_judgment_to_judgment {Σ} : nosubj_judgment Σ → judgment Σ := λ φ, φ.

Definition ivstp τ1 τ2 : nosubj_judgment Σ := (λ ρ, ∀ v, oClose τ1 ρ v → oClose τ2 ρ v)%I.
Program Definition step_indexed_ivstp τ1 i1 τ2 i2 := nosubj_judgment_to_judgment (Σ := Σ)
  (λ ρ, ∀ v, ▷^i1 oClose τ1 ρ v → ▷^i2 oClose τ2 ρ v)%I.
Notation "τ1 , i1 <: τ2 , i2" := (step_indexed_ivstp τ1 i1 τ2 i2) (at level 73, τ2, i1, i2 at next level).

Lemma equiv_vstp Γ τ1 τ2 i1 i2: Γ ⊨ τ1 , i1 <: τ2 , i2 ⊣⊢
    (□∀ ρ v, env_oltyped Γ ρ → ▷^i1 oClose τ1 ρ v → ▷^i2 oClose τ2 ρ v)%I.
Proof.
  iSplit; [iIntros "#H /= !>" (??) "#Hg" |
    iIntros "#H !>" (?) "#Hg /="; iIntros (?)].
  all: iApply ("H" with "Hg").
Qed.

Lemma andstp1 Γ τ1 τ2 i : Γ ⊨ oAnd τ1 τ2 , i <: τ1 , i.
Proof.
  rewrite equiv_vstp /=. by iIntros "!>" (??) "#Hg #[? ?]".
Qed.
End judgments.

End Lty_judge.

From D.Dot Require Import syn synLemmas dlang_inst rules typeExtractionSyn path_wp typeExtractionSem.
From D.Dot.syn Require Import path_repl.
From D.Dot Require unary_lr.
From D.Dot.lr Require path_repl.

Implicit Types
         (v: vl) (e: tm) (d: dm) (ds: dms) (p : path).

Module SemTypes.

Include LtyJudgements VlSorts dlang_inst.

Record dlty Σ := Dlty {
  dlty_label : label;
  dlty_car : env -d> dm -d> iPropO Σ;
  dlty_persistent ρ d :> Persistent (dlty_car ρ d);
}.
Global Arguments Dlty {_} _%I _ {_}.
Global Arguments dlty_car {_} _ _ _ : simpl never.
Global Arguments dlty_label {_} _ /.
Global Existing Instance dlty_persistent.

Definition idtp `{!dlangG Σ} Γ l (φ : dlty Σ) d : iProp Σ :=
  (⌜ l = dlty_label φ ⌝ ∧
    □∀ ρ, ⟦Γ⟧* ρ → dlty_car φ ρ d.|[ρ])%I.
Global Arguments idtp /.
Notation "Γ ⊨ { l := d  } : T" := (idtp Γ l T d) (at level 64, d, l, T at next level).

Definition iptp `{!dlangG Σ} Γ (τ : olty Σ 0) p i: iProp Σ :=
  □∀ ρ, ⟦Γ⟧* ρ -∗
    ▷^i path_wp (p.|[ρ]) (λ v, oClose τ ρ v).

Notation "Γ ⊨p p : τ , i" := (iptp Γ τ p i) (at level 74, p, τ, i at next level).

Section SemTypes.
  Context `{HdotG: dlangG Σ}.

  Implicit Types (τ : olty Σ 0).
   (* (ψ : vl -d> iPropO Σ) (φ : envD Σ)  *)

  Program Definition lift_dinterp_vl (T : dlty Σ): olty Σ 0 :=
    olty0 (λ ρ v, (∃ d, ⌜v @ dlty_label T ↘ d⌝ ∧ dlty_car T ρ d)%I).

  Definition dm_to_type d i (ψ : hoD Σ i) : iProp Σ :=
    (∃ s σ, ⌜ d = dtysem σ s ⌝ ∧ s ↗n[ σ , i ] ψ)%I.
  Notation "d ↗n[ i  ] ψ" := (dm_to_type d i ψ) (at level 20).
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

  Global Opaque dm_to_type.

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

  Lemma oTSel_pv w (l : label) args ρ v :
    oTSel (pv w) l args ρ v ≡
      (∃ ψ d, ⌜w.[ρ] @ l ↘ d⌝ ∧ d ↗n[ 0 ] ψ ∧ ▷ □ ψ vnil v)%I.
  Proof. by rewrite /lty_car/= /vopen path_wp_pv. Qed.

  Lemma Sub_Sel Γ L U va l i:
    Γ ⊨ tv va : oTTMem l L U, i -∗
    Γ ⊨ oLater L, i <: oTSel (pv va) l, i.
  Proof.
    iIntros "#Hva !>" (ρ v) "#Hg #HvL".
    iSpecialize ("Hva" with "Hg"). rewrite /= wp_value_inv'.
    iNext.
    iDestruct "Hva" as (d Hl ψ) "#[Hlψ [#HLψ #HψU]]".
    rewrite oTSel_pv.
    iExists ψ, d; repeat iSplit => //. by iApply "HLψ".
  Qed.

  Lemma Sel_Sub Γ L U va l i:
    Γ ⊨ tv va : oTTMem l L U, i -∗
    Γ ⊨ oTSel (pv va) l, i <: oLater U, i.
  Proof.
    iIntros "#Hva !>" (ρ v) "#Hg #Hψ".
    iSpecialize ("Hva" with "Hg"); rewrite /= wp_value_inv'.
    iNext.
    iDestruct "Hva" as (d Hl ψ) "#[Hlψ [#HLψ #HψU]]".
    rewrite oTSel_pv.
    iDestruct "Hψ" as (ψ1 d1 Hva) "[Hγ #Hψ1v]".
    objLookupDet. iDestruct (dm_to_type_agree d _ _ _ vnil v with "Hlψ Hγ") as "#Hag".
    iApply "HψU" => //. iNext. by iRewrite "Hag".
  Qed.

(*
  (* Alternative (and failed) definition. *)
  Program Definition sem_sel p (l : label) :=
    olty0 (λ ρ v, path_wp p.|[ρ]
      (λ vp, ∃ ψ d, ⌜vp @ l ↘ d⌝ ∧ d ↗ ψ ∧ □ ψ v)%I).

  Lemma Sub_Sel2 Γ L U va l i:
    Γ ⊨ tv va : oTTMem l L U, i -∗
    Γ ⊨ oLater L, i <: oLater (sem_sel (pv va) l), i.
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
    Γ ⊨ oLater ((sem_sel (pv va) l)), i <: oLater U, i.
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
Section Sec.
  Context `{HdotG: dlangG Σ} {i : nat}.
  Implicit Types (φ : hoEnvD Σ i) (τ : olty Σ i).

  Definition leadsto_envD_equiv s σ (φ : hoEnvD Σ i) : iProp Σ :=
    (∃ (φ' : hoEnvD Σ i),
      ⌜φ ≡ (λ args ρ, φ' args (∞ σ.|[ρ]))⌝ ∧ s ↝n[ i ] φ')%I.
  Arguments leadsto_envD_equiv /.
End Sec.

Notation "s ↝[  σ  ] φ" := (leadsto_envD_equiv s σ φ) (at level 20).

Section Sec2.
  Context `{HdotG: dlangG Σ}.

  Import stamp_transfer.

  Lemma extraction_to_leadsto_envD_equiv T g s σ n: T ~[ n ] (g, (s, σ)) →
    wellMappedφ ⟦ g ⟧g -∗ s ↝[ σ ] vopen (ty_interp T).
  Proof.
    move => [T'] [Hl] [<- [_ /is_stamped_nclosed_ty HclT]].
    iIntros "Hm". iExists (vopen (ty_interp T')). iSplitR.
    - iIntros "!%" (args ρ v). exact: unary_lr.interp_subst_commute.
    - iApply (wellMappedφ_apply with "Hm"). by rewrite lookup_fmap Hl.
  Qed.

  Lemma D_Typ_Abs Γ T L U s σ l :
    Γ ⊨ T, 1 <: U, 1 -∗
    Γ ⊨ L, 1 <: T, 1 -∗
    s ↝[ σ ] T -∗
    Γ ⊨ { l := dtysem σ s } : oDTMem l L U.
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
    Γ ⊨ { l := dtysem σ s } : oDTMem l τ τ.
  Proof. iIntros "#Hs"; iApply D_Typ_Abs; by [| iIntros "!> **"]. Qed.
End Sec2.

Section with_lty.
  Context `{dlangG Σ}.
  Import path_repl.
  Implicit Types (φ: vl → iProp Σ).
  (** We don't have yet singleton types in the syntax: so add them as a semantic type
    and prove lemmas about them. Annoyingly, we can't talk about path replacement on
    semantic types. *)

  Lemma rewrite_ty_path_repl_tsel {p q p1 l p2 ρ v}:
    p1 ~pp[ p := q ] p2 →
    alias_paths p.|[ρ] q.|[ρ] → (* p : q.type *)
    oClose (oTSel p1 l) ρ v ≡ oClose (oTSel p2 l) ρ v.
  Proof. exact: path_replacement_equiv. Qed.
  Implicit Types (Γ : sCtx Σ) (τ : olty Σ 0).

  Definition oPSing p : olty Σ 0 :=
    olty0 (λ ρ v, alias_pathsI p.|[ρ] (pv v)).

  Lemma sem_psingleton_eq_1 p ρ v : oClose (oPSing p) ρ v ≡ ⌜ path_wp_pure p.|[ρ] (eq v) ⌝%I.
  Proof. by rewrite /lty_car/=/vopen /alias_pathsI alias_paths_pv_eq_1. Qed.

  Lemma sem_psingleton_eq_2 p ρ v : oClose (oPSing p) ρ v ≡ path_wp p.|[ρ] (λ w, ⌜ v = w ⌝ )%I.
  Proof. by rewrite sem_psingleton_eq_1 path_wp_pureable. Qed.

  Lemma singleton_aliasing Γ p q ρ i :
    Γ ⊨p p : oPSing q, i -∗
    ⟦ Γ ⟧* ρ -∗ ▷^i alias_pathsI p.|[ρ] q.|[ρ].
  Proof.
    iIntros "#Hep #Hg". iSpecialize ("Hep" with "Hg").
    iNext i; iDestruct "Hep" as %Hep; iIntros "!%".
    by apply alias_paths_simpl.
  Qed.

  Lemma singleton_self Γ τ p i :
    Γ ⊨p p : τ, i -∗
    Γ ⊨p p : oPSing p, i.
  Proof.
    iIntros "#Hep !>" (ρ) "Hg". iSpecialize ("Hep" with "Hg"). iNext.
    iDestruct (path_wp_eq with "Hep") as (v Hpv) "_".
    iIntros "!%". by eapply alias_paths_simpl, alias_paths_self, alias_paths_pv_eq_1.
  Qed.

  Lemma iptp2ietp Γ τ p :
    Γ ⊨p p : τ, 0 -∗ Γ ⊨ path2tm p : τ.
  Proof.
    iIntros "#Hep !>" (ρ) "#Hg /="; rewrite path2tm_subst.
    by iApply (path_wp_to_wp with "(Hep Hg)").
  Qed.

  Lemma T_Sub Γ e (T1 T2 : olty Σ 0) i:
    Γ ⊨ e : T1 -∗
    Γ ⊨ T1, 0 <: T2, i -∗
    (*───────────────────────────────*)
    Γ ⊨ iterate tskip i e : T2.
  Proof.
    iIntros "/= #HeT1 #Hsub !>" (ρ) "#Hg".
    rewrite tskip_subst -wp_bind.
    iApply (wp_wand with "(HeT1 Hg)").
    iIntros (v) "#HvT1".
    (* We can swap ▷^i with WP (tv v)! *)
    rewrite -wp_pure_step_later // -wp_value.
    by iApply "Hsub".
  Qed.

  (* XXX Generalize? *)
  Lemma singleton_self_skip Γ τ p i :
    Γ ⊨p p : τ, 0 -∗
    Γ ⊨ iterate tskip i (path2tm p) : oPSing p.
  Proof.
    rewrite singleton_self iptp2ietp.
    iIntros "Hp". iApply (T_Sub with "Hp").
    by iIntros "!> * _ $".
  Qed.

  Lemma singleton_sym Γ p q i:
    Γ ⊨p p : oPSing q, i -∗
    Γ ⊨p q : oPSing p, i.
  Proof.
    iIntros "#Hep !>" (ρ) "#Hg".
    iDestruct (singleton_aliasing with "Hep Hg") as "Hal". iNext i. iDestruct "Hal" as %Hal.
    iIntros "!%". by eapply alias_paths_simpl, alias_paths_symm.
  Qed.

  Lemma singleton_trans Γ p q r i:
    Γ ⊨p p : oPSing q, i -∗
    Γ ⊨p q : oPSing r, i -∗
    Γ ⊨p p : oPSing r, i.
  Proof.
    iIntros "#Hep #Heq !>" (ρ) "#Hg".
    iDestruct (singleton_aliasing with "Hep Hg") as "Hal1".
    iDestruct (singleton_aliasing with "Heq Hg") as "Hal2".
    iNext i. iDestruct "Hal1" as %Hal1. iDestruct "Hal2" as %Hal2.
    iIntros "!%". by eapply alias_paths_simpl, alias_paths_trans.
  Qed.

  Lemma singleton_elim Γ τ p q l i:
    Γ ⊨p p : oPSing q, i -∗
    Γ ⊨p pself q l : τ, i -∗
    Γ ⊨p pself p l : oPSing (pself q l), i.
  Proof.
    iIntros "#Hep #HqlT !>" (ρ) "#Hg".
    iDestruct (singleton_aliasing with "Hep Hg") as "Hal {Hep}".
    iSpecialize ("HqlT" with "Hg").
    rewrite !path_wp_eq /=.
    iNext i. iDestruct "Hal" as %Hal. iDestruct "HqlT" as (vql Hql) "_".
    iIntros "!% /="; setoid_rewrite alias_paths_pv_eq_1.
    by eapply alias_paths_sameres, alias_paths_pself.
  Qed.
  End with_lty.
End SemTypes.
