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

Definition hoEnvD_to_olty {Σ n} (φ : hoEnvD Σ n) : olty Σ n := ho_closed_olty (λ args ρ v, □ φ args ρ v)%I.
(** Here, it is *crucial* that we use finite composition [to_subst σ.|[ρ]], not infinite composition [to_subst σ >> ρ].
    That's because when proving D_Typ, we retrieve the type pointed by [s,
    σ.|[ρ]], and there we must use finite composition. *)
Definition hoEnvD_inst {n Σ} σ (φ : hoEnvD Σ n) : olty Σ n := hoEnvD_to_olty (λ args ρ, φ args (to_subst σ.|[ρ])).

Definition stamp_σ_to_type_n' `{!dlangG Σ} s σ n (τ : olty Σ n) : iProp Σ :=
  (∃ φ, s ↝n[ n ] φ ∗ ▷ (τ ≡ hoEnvD_inst σ φ))%I.
Notation "s ↗n[ σ , n  ] φ" := (stamp_σ_to_type_n' s σ n φ) (at level 20): bi_scope.

Definition dm_to_type `{!dlangG Σ} (d : dm) n (τ : olty Σ n) : iProp Σ :=
  (∃ s σ, ⌜ d = dtysem σ s ⌝ ∗ s ↗n[ σ, n ] τ)%I.
Notation "d ↗n[ n  ] φ" := (dm_to_type d n φ) (at level 20).

Definition leadsto_envD_equiv `{!dlangG Σ} (sσ : extractedTy) n {i : nat} (τ : olty Σ i) : iProp Σ :=
  let '(s, σ) := sσ in
  (⌜nclosed_σ σ n⌝ ∧ s ↗n[ σ , i ] τ)%I.
Global Arguments leadsto_envD_equiv /.

Notation "sσ ↝[  n  ] φ" := (leadsto_envD_equiv sσ n φ) (at level 20).

Section SemTypes.
  Context `{!dlangG Σ}.

  Global Instance stamp_σ_to_type_persistent σ s n ψ : Persistent (s ↗n[ σ , n ] ψ) := _.
  Global Instance: Contractive (stamp_σ_to_type_n' s σ i).
  Proof. rewrite /stamp_σ_to_type_n'. solve_contractive_ho. Qed.

  Import EqNotations.

  Instance hoEnvD_to_olty_ne: NonExpansive (@hoEnvD_to_olty Σ i).
  Proof.
    intros => x y Heq args ρ v. rewrite /olty_car/=.
    repeat f_equiv. exact: Heq.
  Qed.

  Instance hoEnvD_inst_ne: NonExpansive (@hoEnvD_inst i Σ σ).
  Proof.
    rewrite /hoEnvD_inst/=.
    intros => x y Heq. f_equiv => args ρ v. exact: Heq.
  Qed.

  Global Instance dm_to_type_contractive d i : Contractive (dm_to_type d i).
  Proof. solve_contractive. Qed.

  Lemma stamp_σ_to_type_agree_dep_abs {σ s n1 n2 ψ1 ψ2} :
    s ↗n[ σ , n1 ] ψ1 -∗ s ↗n[ σ , n2 ] ψ2 -∗ ∃ eq : n1 = n2,
      ▷ ((rew [olty Σ] eq in ψ1) ≡ ψ2).
  Proof.
    iDestruct 1 as (φ1) "[Hsg1 Heq1]"; iDestruct 1 as (φ2) "[Hsg2 Heq2]".
    iDestruct (stamp_to_type_agree_dep_abs with "Hsg1 Hsg2") as (->) "Hgoal".
    iExists eq_refl. iNext. cbn.
    iRewrite "Heq1"; iRewrite "Heq2".
    by iApply (f_equiv (hoEnvD_inst _) with "Hgoal").
  Qed.

  Lemma olty_equivI i (φ1 φ2 : olty Σ i):
    φ1 ≡ φ2 ⊣⊢@{iPropSI Σ} (φ1 : hoEnvD Σ i) ≡ φ2.
  Proof. by unseal. Qed.

  Lemma stamp_σ_to_type_agree_dep {σ s n1 n2 φ1 φ2} args ρ v :
    s ↗n[ σ , n1 ] φ1 -∗ s ↗n[ σ , n2 ] φ2 -∗ ∃ eq : n1 = n2,
      ▷ ((rew [olty Σ] eq in φ1) args ρ v ≡ φ2 args ρ v).
  Proof.
    iIntros "H1 H2".
    iDestruct (stamp_σ_to_type_agree_dep_abs with "H1 H2") as (->) "H".
    iExists eq_refl. iNext.
    rewrite olty_equivI /=; repeat setoid_rewrite discrete_fun_equivI.
    iApply "H".
  Qed.

  Context {n : nat}.
  Implicit Types (φ : hoEnvD Σ n) (τ : olty Σ n).
   (* (ψ : vl -d> iProp Σ)  *)

  Program Definition lift_dinterp_vl (T : dlty Σ): olty Σ 0 :=
    closed_olty (λ ρ v, (∃ d, ⌜v @ dlty_label T ↘ d⌝ ∧ dlty_car T ρ d)%I).

  Lemma stamp_σ_to_type_intro s σ φ :
    s ↝n[ n ] φ -∗ s ↗n[ σ , n ] hoEnvD_inst σ φ.
  Proof. rewrite /stamp_σ_to_type_n'. iIntros; iExists φ. eauto. Qed.

  Lemma stamp_σ_to_type_agree {σ s τ1 τ2} args ρ v :
    s ↗n[ σ , n ] τ1 -∗ s ↗n[ σ , n ] τ2 -∗ ▷ (τ1 args ρ v ≡ τ2 args ρ v).
  Proof.
    iIntros "Hs1 Hs2".
    iDestruct (stamp_σ_to_type_agree_dep args ρ v with "Hs1 Hs2") as (eq) "H".
    rewrite (proof_irrel eq eq_refl) /=. by [].
  Qed.

  (* Global Opaque stamp_σ_to_type_n'. *)

  Global Instance dm_to_type_persistent d τ : Persistent (d ↗n[ n ] τ) := _.

  Lemma dm_to_type_agree d τ1 τ2 args ρ v : d ↗n[ n ] τ1 -∗ d ↗n[ n ] τ2 -∗ ▷ (τ1 args ρ v ≡ τ2 args ρ v).
  Proof.
    iDestruct 1 as (s σ ?) "#Hs1"; iDestruct 1 as (s' σ' ?) "#Hs2".
    simplify_eq. by iApply (stamp_σ_to_type_agree args with "Hs1 Hs2").
  Qed.

  Lemma dm_to_type_intro d s σ (φ : hoEnvD Σ n) :
    d = dtysem σ s → s ↝n[ n ] φ -∗ d ↗n[ n ] hoEnvD_inst σ φ.
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

  (** Type members with contractive upper F-bounds. *)

  Lemma upred_wand_iff_internal_eq {M} A B: (■(A ∗-∗ B)) ⊢@{uPredI M} (A ≡ B).
  Proof. iIntros. by iApply prop_ext. Qed.

  Lemma upred_iff_internal_eq {M} A B: ■(A ↔ B) ⊢@{uPredI M} (A ≡ B).
  Proof.
    iIntros "#Heq". iApply prop_ext.
    iModIntro; iSplit; iIntros; by iApply "Heq".
  Qed.

  Lemma internal_eq_contractive_eq {i} (UF : hoD Σ i -> olty Σ i) A B
    {HΨ: Contractive UF} :
    ▷ (A ≡ B) ⊢@{iPropI Σ} UF A ≡ UF B.
  Proof.
    (* Based on internal_eq_rewrite_contractive. *)
    rewrite later_eq_2. move: HΨ=>/contractive_alt [g [? HΨ]].
    rewrite !HΨ. iIntros "H". by iRewrite "H".
  Qed.

  Lemma UF_contractive_equivI {i} (UF : hoD Σ i -> olty Σ i) `{!Contractive UF}
        A B args ρ v:
    (▷ ■ ∀ args v, (A args v ∗-∗ B args v)) -∗
    UF A args ρ v ≡ UF B args ρ v.
  Proof.
    iIntros "#Hsub".
    iPoseProof (internal_eq_contractive_eq UF A B with "[]") as "H"; rewrite ?olty_equivI;
      repeat setoid_rewrite bi.discrete_fun_equivI; last iApply "H".
    iNext; iIntros. iApply prop_ext. iApply ("Hsub" $! _ _).
  Qed.

  Definition applyUF {i} (UF : hoD Σ i -> olty Σ i)
      (A : olty Σ i) : hoEnvD Σ i :=
    λ args ρ, UF (λ args, A args ρ) args ρ.
  Global Arguments applyUF /.

  Program Definition oApplyUF {i} (UF : hoD Σ i -> olty Σ i) (A : olty Σ i) : olty Σ i :=
    Olty (applyUF UF A) _.
  Next Obligation. intros **?**. by rewrite /applyUF olty_vclosed. Qed.

  Lemma UF_contractive_equivI2 {i} (UF : hoD Σ i -> olty Σ i) A B
    `{Contractive UF} args ρ v:
    UF A args ρ v ⊢@{iPropI Σ}
      (▷ ■ ∀ args v, (A args v ∗-∗ B args v)) -∗
      UF B args ρ v.
  Proof.
    iIntros "HUFA Heq".
    by iRewrite -(UF_contractive_equivI _ _ _ args ρ v with "Heq").
  Qed.

  Definition SSel s σ i : hoEnvD Σ i := λ args ρ v,
    (∃ ψ, s ↗n[ σ, i ] ψ ∧ ▷ ψ args ids v)%I.

  Program Definition oSSel s σ i := ho_closed_olty (SSel s σ i).

  Program Definition oSSelRec s σ i (UF : hoD Σ i -> olty Σ i)
          (ψ : olty Σ i) : olty Σ i :=
    (oAnd (oApplyUF UF ψ) (oSSel s σ i)
      (* ∧ ▷ (∀ args ρ v, φ args ids v ≡ ψ args ρ v) *)
    (* ∃ φ : olty Σ i,
      s ↗n[ σ , i ] φ
      ∧ ▷ (∀ args ρ v, φ args ids v ≡ ψ args ρ v) *)
      )%I.
  (* Lemma olty_dist_alt τ1 τ2: olty_car τ1 = olty_car τ2 → τ1 = τ2.
  Proof.
    move: τ1 τ2 => [φ1 Hp1 Hvc1] [φ2 Hp2 Hvc2]. rewrite /olty_car /=.
    intros ->. f_equal; exact: ProofIrrelevance.proof_irrelevance.
  Qed. *)

  Instance hsubst_olty_ne i σ : NonExpansive (hsubst σ : olty Σ i → olty Σ i).
  Proof. move => n x y Heq args ρ v. exact: Heq. Qed.

  Instance oSSelRec_contractive i UF {Hc: Contractive UF}: Contractive (oSSelRec s σ i UF).
  Proof.
    intros => x y Heq args ρ v.
    rewrite /olty_car/=; f_equiv.
    rewrite /olty_car/=/applyUF.
    apply: Hc. case: n Heq => [//|n /= Heq ?]. exact: Heq.
    (* - f_equiv. f_contractive. exact: Heq.
      f_contractive. by f_equiv. *)
      (* f_equiv => φ. f_equiv. f_contractive.
      do 3 (f_equiv => ?). f_equiv. exact: Heq. *)
  Qed.

  Definition oSSelR s σ i UF `{Contractive UF} : olty Σ i := fixpoint (oSSelRec s σ i UF).
  Lemma oSSelR_unfold s σ i UF `{Contractive UF} :
    oSSelR s σ i UF ≡ oSSelRec s σ i UF (oSSelR s σ i UF).
  Proof. apply fixpoint_unfold. Qed.

  Program Definition oDSelUF d i UF `{!Contractive UF} : olty Σ i :=
    Olty (λ args ρ v,
    ∃ σ s, ⌜d = dtysem σ s⌝ ∧ oSSelR s σ i UF args ρ v)%I _.
  Next Obligation.
    intros **?**. iDestruct 1 as (???) "H". by rewrite olty_vclosed.
  Qed.

  Program Definition oTSelUF_path p l i UF `{!Contractive UF} : olty Σ i :=
    ho_closed_olty (λ args ρ v, path_wp p.|[ρ]
      (λ vp, ∃ d, ⌜vp @ l ↘ d ⌝ ∧ oDSelUF d i UF args ρ v))%I.
  Program Definition oTSelUF w l i UF `{!Contractive UF} : olty Σ i :=
    Olty (λ args ρ v, ∃ d, ⌜w.[ρ] @ l ↘ d ⌝ ∧ oDSelUF d i UF args ρ v)%I _.
  Next Obligation.
    intros **?**. iDestruct 1 as (d ? σ s ?) "H". by rewrite olty_vclosed.
  Qed.

  Lemma oSSelR_oTSelUF_equiv w l σ s UF `{Contractive UF} args ρ v:
    w.[ρ] @ l ↘ dtysem σ s →
    oSSelR s σ 0 UF args ρ v ≡ oTSelUF w l 0 UF args ρ v.
  Proof.
    intros Hl1; iSplit.
    + iIntros "Hψ".
      do 2 (rewrite /olty_car/=). eauto 6.
    + (* repeat rewrite /olty_car/=. *)
      iDestruct 1 as (d Hl2 σ' s' ?) "H". by objLookupDet.
  Qed.

  Lemma oSSelR_oTSelUF_wand_iff w l σ s UF `{Contractive UF} args ρ v:
    w.[ρ] @ l ↘ dtysem σ s →
    (oSSelR s σ 0 UF args ρ v ∗-∗ oTSelUF w l 0 UF args ρ v)%I.
  Proof.
    intros. rewrite (oSSelR_oTSelUF_equiv w l σ s UF args ρ v) //.
    exact: wand_iff_refl.
  Qed.

  Lemma Sel_Sub_Rec0 (* L *) UF `{Contractive UF} va l args ρ v :
    (* Γ ⊨ tv va : oTTMemUp1 l L UF, i -∗ *)
    oTSelUF va l 0 UF args ρ v -∗ oApplyUF UF (oTSelUF va l 0 UF) args ρ v.
  Proof.
    iDestruct 1 as (d Hlookup σ s ->) "Hψ1v".
    rewrite (oSSelR_unfold _ _ 0 UF _ _ _).
    iDestruct "Hψ1v" as "[HUF _]".
    rewrite /olty_car/=.
    iApply (UF_contractive_equivI2 with "HUF"). clear args. iIntros (args w).
    iModIntro. iModIntro. by iApply oSSelR_oTSelUF_wand_iff.
  Qed.

  Lemma Sel_Sub_Rec Γ (* L *) UF `{Contractive UF} va l i:
    (* Γ ⊨ tv va : oTTMemUp1 l L UF, i -∗ *)
    Γ ⊨ [oTSelUF va l 0 UF, i] <:
        [oApplyUF UF (oTSelUF va l 0 UF), i].
  Proof. iIntros " !>" (ρ v Hclv) "_ #H". by rewrite Sel_Sub_Rec0. Qed.

  (* Definition oDTMemUp1 l τ1 (UF : hoD Σ 0 → olty Σ 0) : dlty Σ := Dlty l
    (λ ρ d,
    ∃ ψ, (d ↗n[ 0 ] ψ) ∗
       □ ((∀ v, ⌜ nclosed_vl v 0 ⌝ → ▷ τ1 vnil ρ v → ▷ ψ vnil ids v) ∗
          (∀ v, ⌜ nclosed_vl v 0 ⌝ → ▷ ψ vnil ids v → ▷ UF (λ args v, ψ args ids v) vnil ρ v)))%I.

  Definition oTTMemUp1 l τ1 UF := lift_dinterp_vl (oDTMemUp1 l τ1 UF).

  Lemma Sub_TTMemUp1 Γ L UF l i:
    Γ ⊨ [oTTMemUp1 l L UF, i] <: [oTTMem l L oTop, i].
  Proof.
    rewrite /= /olty_car/= /vopen/= /dlty_car/=.
    iIntros "!>" (ρ v Hclv) "#Hg [$ H] /= !>".
    iDestruct "H" as (d Hlook ψ) "[Hl [#HLψ _]]".
    repeat (iExists _; iSplit => //).
    iModIntro; iSplitL; eauto.
  Qed. *)

  Definition oDTMemUp l τ1 UF `{Contractive UF}: dlty Σ := Dlty l
    (λ ρ d,
      ∃ ψ, (d ↗n[ 0 ] ψ) ∧
      □ ((∀ v, τ1 vnil ρ v → oDSelUF d 0 UF vnil ρ v) ∧
         (∀ v, ⌜ nclosed_vl v 0 ⌝ → ▷ τ1 vnil ρ v → ▷ ψ vnil ids v)))%I.

  Definition oTTMemUp l τ1 UF `{Contractive UF} :=
    lift_dinterp_vl (oDTMemUp l τ1 UF).

  Lemma Sub_TTMemUp Γ L UF l i `{Contractive UF}:
    Γ ⊨ [oTTMemUp l L UF, i] <: [oTTMem l L oTop, i].
  Proof.
    rewrite /= /olty_car/= /vopen/= /dlty_car/=.
    iIntros "!>" (ρ v Hclv) "#Hg [$ H] /= !>".
    iDestruct "H" as (d Hlook ψ) "#[Hψ #[_ HLψ]]".
    repeat (iExists _; iSplit => //).
    iModIntro; iSplitL; eauto.
  Qed.
    (* iIntros (w Hclw) "HL".
    iSpecialize ("HLψ" $! vnil w).
    rewrite /olty_car/=.
    iDestruct ("HLψ" with "HL") as (s σ) "[>% #H] {HLψ}"; subst.

    rewrite (oSSelR_unfold _ _ 0 UF _ _ _).
    rewrite /olty_car/=/applyUF.
  Abort. *)


  Lemma Sub_SelUp Γ L UF `{Contractive UF} va l i:
    Γ ⊨ tv va : oTTMemUp l L UF, i -∗
    Γ ⊨ [L, i] <: [oTSelUF va l 0 UF, i].
  Proof.
    iIntros "#[% #Hva] !>" (ρ v Hclv) "#Hg #HvL".
    iSpecialize ("Hva" with "Hg"). rewrite /= wp_value_inv'.
    iNext.
    iDestruct "Hva" as (Hclvas d Hl ψ) "[_ #[HLU HLψ]]". cbn in Hl.
    iSpecialize ("HLU" with "HvL"). by iExists d; iSplit.
  Qed.

  Lemma D_TypUp Γ T L UF `{!Contractive UF} s σ l:
    Γ ⊨ [T, 0] <: [oApplyUF UF T, 0] -∗
    Γ ⊨ [L, 0] <: [T, 0] -∗
    (s, σ) ↝[ length Γ ] T -∗
    Γ ⊨d{ l := dtysem σ s } : oDTMemUp l L UF.
  Proof.
    iIntros "#HTU #HLT #[% Hs] /="; repeat iSplit; [auto using fv_dtysem..|].
    iIntros "!>" (ρ) "#Hg". iDestruct "Hs" as (φ) "[Hγ Heq]".
    rewrite /dlty_car /=.
    iExists _; iSplit. by iApply dm_to_type_intro.
    (* rewrite [olty_car (_ _)]/olty_car /=. *)
    (* rewrite [(_ _) _]/olty_car /=. *)
    (* rewrite olty_equivI; repeat setoid_rewrite discrete_fun_equivI. *)
    iModIntro; iSplit;
    iIntros (v); last iIntros (Hclv); iIntros "#HL".
    - iAssert (⌜nclosed_vl v 0⌝)%I as %Hclv.
      by rewrite olty_vclosed.
      iDestruct ("HLT" $! ρ v Hclv with "Hg HL") as "{HLT} #HLT".
      iExists _, s. iSplit => //.
      iLöb as "IH".
      iEval (rewrite (oSSelR_unfold _ _ 0 UF _ _ _) /olty_car/=).
      iSplit.
      + iSpecialize ("HTU" $! ρ v Hclv with "Hg HLT").
        iEval (rewrite /olty_car/=) in "HTU".
        iEval (rewrite /olty_car/=).
        iApply (UF_contractive_equivI2 with "HTU").
        admit. (* FAIL! *)
      (* iExists _.
      iExists (oSSelR s σ _ UF).
      iSplit. admit. *)
      + iExists _. iFrame "Hγ". iNext.
        Fail iRewrite "Heq".
        iEval (rewrite olty_equivI /olty_car/=).
        admit.
    - iNext.
      rewrite olty_equivI; repeat setoid_rewrite discrete_fun_equivI.
      iSpecialize ("Heq" $! vnil (to_subst ρ) v).
      iPoseProof (internal_eq_iff with "Heq") as "Heq'".
      iEval (rewrite /hoEnvD_inst/=/olty_car/=).
      iEval (rewrite /hoEnvD_inst/=/olty_car/=) in "Heq'".
      iEval (asimpl). iApply "Heq'".
      by iApply "HLT".
    Admitted.
(*
      About internal_eq_iff.
        iSpecialize ("Heq'" $! vnil (ids: env) v).
        rewrite /olty_car/=. /hoEnvD_inst/=. asimpl.
        rewrite /flip_
        iRewrite "Heq'". *)

    (* iClear "HLT HTU Hg". *)
      (* iNext.
      iRewrite ("Heq" $! vnil (to_subst ρ) v).
      rewrite /olty_car/=. asimpl. iExact "HL".
      (* + iNext. iIntros.
        unshelve iPoseProof (f_equiv (λ x, x.|[to_subst ρ]) with "Heq") as "Heq' {Heq}".
        apply _. admit.
        rewrite olty_equivI; repeat setoid_rewrite discrete_fun_equivI.
        iSpecialize ("Heq'" $! args (ids: env) v0).
        iRewrite "Heq'". *)


      iExists T.|[to_subst ρ]. iSplit.
      + iExists _. iFrame "Hγ". iNext.
        (* Fail iRewrite "Heq". *)
        admit.
      + iNext. iIntros.
        unshelve iPoseProof (f_equiv (λ x, x.|[to_subst ρ]) with "Heq") as "Heq' {Heq}".
        apply _. admit.
        rewrite olty_equivI; repeat setoid_rewrite discrete_fun_equivI.
        iSpecialize ("Heq'" $! args (ids: env) v0).
        iRewrite "Heq'".

      asimpl.
      rewrite /flip_hoEnvD_inst/hoEnvD_inst/=. asimpl.
      iRewrite ("Heq" $! vnil (to_subst ρ) v) in "HLT".
      rewrite /olty_car /=. asimpl. iExact "HLT".
    - iApply "HTU" => //. iClear "HLT HTU Hg".
      iNext.
      iRewrite ("Heq" $! vnil (to_subst ρ) v).
      rewrite /olty_car/=. asimpl. iExact "HL".

    - iDestruct ("HLT" $! ρ v Hclv with "Hg HL") as "{HLT HTU HL} HLT".
      iNext.
      iRewrite ("Heq" $! vnil (to_subst ρ) v) in "HLT".
      rewrite /olty_car /=. asimpl. iExact "HLT".
    - iApply "HTU" => //. iClear "HLT HTU Hg".
      iNext.
      iRewrite ("Heq" $! vnil (to_subst ρ) v).
      rewrite /olty_car/=. asimpl. iExact "HL".
  Qed. *)

(*
  Program Definition oTSelRec p l i
        (UF : hoD Σ i -> olty Σ i) : olty Σ i -> olty Σ i := λ ψ,
    Olty (λ args ρ v, applyUF UF ψ args ρ v ∧ path_wp p.|[ρ]
      (λ vp, ∃ d ψ', ⌜vp @ l ↘ d ⌝ ∧ d ↗n[ i ] ψ' ∧
        ▷ (∀ args ρ v, ψ args ρ v ≡ ψ' args ids v) ∧
        ▷ ψ args ρ v))%I _.
  Next Obligation. intros **?**. rewrite olty_vclosed. iIntros "[$ _]". Qed.

  Instance oTSelRec_contractive i (UF : hoD Σ i -> olty Σ i) {Hc: Contractive UF}: Contractive (oTSelRec p l i UF).
  Proof.
    intros => x y Heq args ρ v.
    rewrite ![_ (oTSelRec _ _ _ _ _)]/olty_car/=.
    rewrite ![_ (applyUF _ _)]/olty_car/=.
    f_equiv. apply: Hc. case: n Heq => [//|n /= Heq ?]. exact: Heq.
    f_equiv => vp; f_equiv => d; f_equiv => ψ'; f_equiv; f_equiv; f_equiv.
    f_contractive. do 3 (f_equiv => ?). f_equiv. exact: Heq.
    f_contractive. exact: Heq.
  Qed.

  Definition oTSelR p l i UF `{Contractive UF} : olty Σ i :=
    fixpoint (oTSelRec p l i UF).

  Lemma oTSelR_unfold p l i UF `{Contractive UF} :
    oTSelR p l i UF ≡ oTSelRec p l i UF (oTSelR p l i UF).
  Proof. apply fixpoint_unfold. Qed. *)

  (* OOOOOOOOOOO *)

  (* Lemma Sel_Sub_Rec1 Γ UF `{Contractive UF} va l i:
    (* Γ ⊨ tv va : oTTMemUp1 l L UF, i -∗ *)
    Γ ⊨ [oTSelR (pv va) l 0 UF, i] <: [applyUF UF (oTSelR (pv va) l 0 UF), i].
  Proof.
    iIntros "!>" (ρ v Hclv) "#Hg #Hψ".
    iNext.
    rewrite (oTSelR_unfold _ _ _ UF _ _ _) [_ (oTSelRec _ _ _ _ _)]/olty_car/=.
    (* iDestruct "Hψ" as (_ d ψ Hlookup) "[Hdψ [Heq [HUF Hstamp]]]". *)
    iDestruct "Hψ" as "[HUF _]".
    iExact "HUF".
  Qed. *)
  (* Too easy - the other subtyping rule will be harder? *)

  (* Lemma Sub_SelUp Γ L UF `{Contractive UF} va l i:
    Γ ⊨ tv va : oTTMemUp1 l L UF, i -∗
    Γ ⊨ [oLater L, i] <: [oTSelR (pv va) l 0 UF, i].
  Proof. *)
    (* iIntros "#[% #Hva] !>" (ρ v Hclv) "#Hg #[_ HvL]".
    iSpecialize ("Hva" with "Hg"). rewrite /= wp_value_inv'.
    iNext.
    iLöb as "IH".
    iEval (rewrite (oTSelR_unfold _ _ _ UF _ _ _) [_ (oTSelRec _ _ _ _ _)]/olty_car/=).
    iDestruct "Hva" as (Hclvas' d Hl ψ') "#[Hlψ [#HLψ #HψU]]".
    iExists d, ψ'; repeat iSplit => //.
    iFrame (Hclv).
    - iClear "IH".
    iEval (setoid_rewrite (oTSelR_unfold _ _ _ UF _ _ _)). rewrite /oTSelRec/=.
    Transparent dm_to_type.
    iDestruct "Hlψ" as (s σ Heq) "H". *)
      (* rewrite (oTSelR_unfold (pv va) l 0 UF) /oTSelRec /=. *)
  (* Abort. *)
    (* by iApply "HLψ". Qed. *)


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

Section Sec2.
  Context `{HdotG: dlangG Σ}.

  Lemma D_Typ Γ T L U s σ l :
    Γ ⊨ [T, 1] <: [U, 1] -∗
    Γ ⊨ [L, 1] <: [T, 1] -∗
    (s, σ) ↝[ length Γ ] T -∗
    Γ ⊨d{ l := dtysem σ s } : oDTMem l L U.
  Proof.
    iIntros "#HTU #HLT #[% Hs] /="; repeat iSplit; [auto using fv_dtysem..|].
    iIntros "!>" (ρ) "#Hg". iDestruct "Hs" as (φ) "[Hγ Heq]".
    rewrite /dlty_car /=.
    iExists _; iSplit. by iApply dm_to_type_intro.
    (* rewrite [olty_car (_ _)]/olty_car /=. *)
    (* rewrite [(_ _) _]/olty_car /=. *)
    rewrite olty_equivI; repeat setoid_rewrite discrete_fun_equivI.
    iModIntro; repeat iSplitL; iIntros (v Hclv) "#HL {Hγ}".
    - iDestruct ("HLT" $! ρ v Hclv with "Hg HL") as "{HLT HTU HL} HLT".
      iNext.
      iRewrite ("Heq" $! vnil (to_subst ρ) v) in "HLT".
      rewrite /olty_car /=. asimpl. iExact "HLT".
    - iApply "HTU" => //. iClear "HLT HTU Hg".
      iNext.
      iRewrite ("Heq" $! vnil (to_subst ρ) v).
      rewrite /olty_car/=. asimpl. iExact "HL".
  Qed.

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
    iSplit => //; iExists (oty_interp (h T')); iSplitL; [iApply "Hm"|];
      iIntros "!% //=" (args ρ v).
    rewrite (oty_interp_subst_commute' (h T')) //=; last solve_fv_congruence.
    iSplit; last iIntros "[_ #$]".
    iIntros "#$". by rewrite -olty_vclosed.
    (* rewrite /oty_interp/hoEnvD_inst/olty_car/= /vopen/=. *)
  Qed.
End Sec2.
End SemTypes.
