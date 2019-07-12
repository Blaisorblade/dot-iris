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

Module Type OLty_judge (Import VS: VlSortsFullSig) (Import LVS : LiftWp VS).
Include OLty VS LVS.

Class Closeable s := nclosed_s : s → nat → Prop.
Instance closeable_sort s `{Sort s} : Closeable s := nclosed.
Instance closeable_vl : Closeable vl := nclosed_vl.

Implicit Types (v: vl) (vs : vls) (ρ : env).

Section judgments.
Context `{dlangG Σ} `{OTyInterp ty Σ}.
Implicit Type (τ : olty Σ 0).

Notation ctx := (list (ty 0)).

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

Program Definition ivtp τ v : judgment Σ vl := subj_judgment_to_judgment (v, oClose τ).
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

Definition ivstp τ1 τ2 : nosubj_judgment Σ := (λ ρ, ∀ v, ⌜ nclosed_vl v 0 ⌝ → oClose τ1 ρ v → oClose τ2 ρ v)%I.
Program Definition step_indexed_ivstp τ1 i1 τ2 i2 := nosubj_judgment_to_judgment (Σ := Σ)
  (λ ρ, ∀ v, ⌜ nclosed_vl v 0 ⌝ → (▷^i1 oClose τ1 ρ v) → ▷^i2 oClose τ2 ρ v)%I.
Notation "[ τ1 , i1 ] <: [ τ2 , i2 ]" := (step_indexed_ivstp τ1 i1 τ2 i2) (at level 73).

Lemma equiv_vstp Γ τ1 τ2 i1 i2: Γ ⊨ [τ1 , i1] <: [τ2 , i2] ⊣⊢
    (□∀ vs v, ⌜ nclosed_vl v 0 ⌝ → env_oltyped_fin Γ vs → (▷^i1 oClose τ1 (to_subst vs) v) → ▷^i2 oClose τ2 (to_subst vs) v)%I.
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

From D.Dot Require Import syn operational synLemmas rules typeExtractionSyn path_wp.
From D.Dot Require unary_lr.

Implicit Types
         (v: vl) (e: tm) (d: dm) (ds: dms) (p : path).

Module SemTypes.

Include OLtyJudgements VlSorts operational.

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

Definition hoEnvD_to_olty {Σ n} φ : olty Σ n := ho_closed_olty (λ args ρ v, □ φ args ρ v)%I.

Definition stamp_σ_to_type_n' `{!dlangG Σ} s σ n (τ : olty Σ n) : iProp Σ :=
  (∃ φ, ⌜ τ = hoEnvD_to_olty φ.|[to_subst σ] ⌝ ∗ s ↝n[ n ] φ)%I.
Notation "s ↗n[ σ , n  ] φ" := (stamp_σ_to_type_n' s σ n φ) (at level 20): bi_scope.

Definition dm_to_type `{!dlangG Σ} (d : dm) n (τ : olty Σ n) : iProp Σ :=
  (∃ s σ, ⌜ d = dtysem σ s ⌝ ∗ s ↗n[ σ, n ] τ)%I.
Notation "d ↗n[ n  ] φ" := (dm_to_type d n φ) (at level 20).

Section SemTypes.
  Context `{!dlangG Σ}.

  Global Instance stamp_σ_to_type_persistent σ s n ψ : Persistent (s ↗n[ σ , n ] ψ) := _.

  Import EqNotations.
  Lemma stamp_σ_to_type_agree_dep {σ s n1 n2 φ1 φ2} args ρ v :
    s ↗n[ σ , n1 ] φ1 -∗ s ↗n[ σ , n2 ] φ2 -∗ ∃ eq : n1 = n2,
      ▷ ((rew [hoEnvD Σ] eq in φ1) args ρ v ≡ φ2 args ρ v).
  Proof.
    iDestruct 1 as (φ1' ->) "Hsg1"; iDestruct 1 as (φ2' ->) "Hsg2".
    iDestruct (stamp_to_type_agree_dep args (to_subst σ >> ρ) v with "Hsg1 Hsg2") as (Heq) "Hgoal".
    iExists Heq; destruct Heq; rewrite /olty_car /hsubst /hsubst_hoEnvD /=. iNext. by iRewrite "Hgoal".
  Qed.

  Context {n : nat}.
  Implicit Types (φ : hoEnvD Σ n) (τ : olty Σ n).
   (* (ψ : vl -d> iProp Σ)  *)

  Program Definition lift_dinterp_vl (T : dlty Σ): olty Σ 0 :=
    closed_olty (λ ρ v, (∃ d, ⌜v @ dlty_label T ↘ d⌝ ∧ dlty_car T ρ d)%I).

  Lemma stamp_σ_to_type_intro s σ φ :
    s ↝n[ n ] φ -∗ s ↗n[ σ , n ] hoEnvD_to_olty φ.|[to_subst σ].
  Proof. rewrite /stamp_σ_to_type_n'. iIntros; iExists φ. eauto. Qed.

  Lemma stamp_σ_to_type_agree {σ s τ1 τ2} args ρ v :
    s ↗n[ σ , n ] τ1 -∗ s ↗n[ σ , n ] τ2 -∗ ▷ (τ1 args ρ v ≡ τ2 args ρ v).
  Proof.
    iIntros "Hs1 Hs2".
    iDestruct (stamp_σ_to_type_agree_dep args ρ v with "Hs1 Hs2") as (eq) "H".
    rewrite (proof_irrel eq eq_refl) /=. by [].
  Qed.

  (* Global Opaque stamp_σ_to_type_n'. *)

  Global Instance dm_to_type_persistent d τ: Persistent (d ↗n[ n ] τ) := _.

  Lemma dm_to_type_agree d τ1 τ2 args ρ v : d ↗n[ n ] τ1 -∗ d ↗n[ n ] τ2 -∗ ▷ (τ1 args ρ v ≡ τ2 args ρ v).
  Proof.
    iDestruct 1 as (s σ ?) "#Hs1"; iDestruct 1 as (s' σ' ?) "#Hs2".
    simplify_eq. by iApply (stamp_σ_to_type_agree args with "Hs1 Hs2").
  Qed.

  Lemma dm_to_type_intro d s σ (φ : hoEnvD Σ n) :
    d = dtysem σ s → s ↝n[ n ] φ -∗ d ↗n[ n ] hoEnvD_to_olty φ.|[to_subst σ].
  Proof. iIntros. iExists s, σ. iFrame "%". by iApply stamp_σ_to_type_intro. Qed.

  Global Opaque dm_to_type.
End SemTypes.

Section SemTypes2.
  Context `{HdotG: dlangG Σ}.
  Implicit Types (τ : olty Σ 0).
  (* Rewrite using (higher) semantic kinds! *)
  Definition oDTMem l τ1 τ2 : dlty Σ := Dlty l
    (λ ρ d,
    ∃ τ, (d ↗n[ 0 ] τ) ∗
       □ ((∀ v, ⌜ nclosed_vl v 0 ⌝ → ▷ τ1 vnil ρ v → ▷ τ vnil ids v) ∗
          (∀ v, ⌜ nclosed_vl v 0 ⌝ → ▷ τ vnil ids v → ▷ τ2 vnil ρ v)))%I.

  Definition oTTMem l τ1 τ2 :=
    lift_dinterp_vl (oDTMem l τ1 τ2).

  Definition oDVMem l τ : dlty Σ := Dlty l
    (λ ρ d, ∃ vmem, ⌜d = dvl vmem⌝ ∧ ▷ oClose τ ρ vmem)%I.

  Definition oTVMem l τ :=
    lift_dinterp_vl (oDVMem l τ).
(*
  Program Definition oInterp T := Olty ⟦ T ⟧ _.
  Next Obligation. rewrite /vclosed=>*. by rewrite interp_vclosed. Qed. *)

  Definition oTSel p (l : label) :=
    closed_olty (λ ρ v, path_wp p.|[ρ]
      (λ vp, ∃ ψ d, ⌜vp @ l ↘ d⌝ ∧ d ↗n[ 0 ] ψ ∧ ▷ ψ vnil (* ρ *) ids v))%I.

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
    objLookupDet; subst. iDestruct (dm_to_type_agree d _ _ vnil ids v with "Hlψ Hγ") as "#Hag".
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
End SemTypes2.

Module Import LogRelAdapt.
Import unary_lr.

Inductive hty : nat → Type :=
| h : ty → hty 0.
Instance hsubst_hty {i}: HSubst vl (hty i) := λ sb '(h T), h (T.|[sb]).

Global Program Instance oty_interp_dot `{!dlangG Σ}: OTyInterp hty Σ :=
  λ _ '(h T), Olty (vopen ⟦ T ⟧) _.
Next Obligation. rewrite /vclosed/vopen=>*. by rewrite interp_v_closed. Qed.

Lemma oty_interp_subst_commute `{!dlangG Σ} T σ args sb v:
  nclosed T (length σ) →
  oty_interp (h T.|[to_subst σ]) args sb v ≡ oty_interp (h T) args (to_subst σ.|[sb]) v.
Proof. rewrite /olty_car/=. exact: interp_subst_commute. Qed.

Lemma oty_interp_subst_commute' `{!dlangG Σ} (T : hty 0) σ args sb v:
  nclosed T (length σ) →
  oty_interp T.|[to_subst σ] args sb v ≡ oty_interp T args (to_subst σ.|[sb]) v.
Proof.
  case: T args => T args; rewrite /olty_car/= => Hcl.
  apply interp_subst_commute; auto with fv.
Qed.
End LogRelAdapt.

(*
  Even if semantic types use infinite substitutions, we can still reuse the
  current stamping theory, based on finite substitutions.
*)
Section Sec.
  Context `{!dlangG Σ} .

  Definition leadsto_envD_equiv (sσ : extractedTy) n {i : nat} (τ : olty Σ i) : iProp Σ :=
    let '(s, σ) := sσ in
    (⌜nclosed_σ σ n⌝ ∧ s ↗n[ σ , i ] τ)%I.
  Arguments leadsto_envD_equiv /.
End Sec.

Notation "sσ ↝[  n  ] φ" := (leadsto_envD_equiv sσ n φ) (at level 20).

Section Sec2.
  Context `{HdotG: dlangG Σ}.

  Lemma D_Typ Γ T L U s σ l :
    Γ ⊨ [T, 1] <: [U, 1] -∗
    Γ ⊨ [L, 1] <: [T, 1] -∗
    (s, σ) ↝[ length Γ ] T -∗
    Γ ⊨d{ l := dtysem σ s } : oDTMem l L U.
  Proof.
    iIntros "#HTU #HLT #[% Hs] /="; repeat iSplit; [auto using fv_dtysem..|].
    iIntros "!>" (ρ) "#Hg"; iDestruct "Hs" as (φ ->) "Hγ".
    rewrite /dlty_car /=.
    iExists _; iSplit. by iApply dm_to_type_intro.
    (* rewrite [olty_car (_ _)]/olty_car /=. *)
    (* rewrite [(_ _) _]/olty_car /=. *)
    iModIntro; repeat iSplitL; iIntros (v Hclv) "#HL".
    - iDestruct ("HLT" $! ρ v Hclv with "Hg HL") as "{HLT HTU HL} [$ HLT]".
      rewrite /hsubst /hsubst_hoEnvD/=. asimpl.

      Fail iApply "HLT".
      admit.
    - iApply "HTU" => //. iClear "HLT HTU Hg Hγ".
      rewrite /hsubst /hsubst_hoEnvD/olty_car/=. asimpl.
      Fail iApply "HL".
    Abort.

  Lemma D_Typ_Concr Γ (τ : olty Σ 0) s σ l:
    (s, σ) ↝[ length Γ ] τ -∗
    Γ ⊨d{ l := dtysem σ s } : oDTMem l τ τ.
  Proof. iIntros "#Hs"; iApply D_Typ; by [| iIntros "!> **"]. Qed.

  Definition wellMapped (g : stys) : iProp Σ :=
    (□∀ s T, ⌜ g !! s = Some T⌝ → s ↝n[ 0 ] oty_interp (h T))%I.
  Instance wellMapped_persistent g: Persistent (wellMapped g) := _.
  Global Arguments wellMapped: simpl never.

  Lemma extraction_to_leadsto_envD_equiv T g sσ n: T ~[ n ] (g, sσ) →
    wellMapped g -∗ sσ ↝[ n ] oty_interp (h T).
  Proof.
    move: sσ => [s σ] [T'] [Hl] [<-] [Hclσ HclT]. iIntros "Hm".
    iSplit => //; iExists (oty_interp (h T')); iSplitL; [iApply "Hm" | ];
    iIntros "!% //" (args ρ v).
    apply (oty_interp_subst_commute' (h T')). solve_fv_congruence.
    (* exact: oty_interp_subst_commute. *)
  Qed.
End Sec2.
End SemTypes.
