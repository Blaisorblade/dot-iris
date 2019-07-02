From D Require Import iris_prelude asubst_base asubst_intf dlang.
(* From D.pure_program_logic Require Import lifting. *)
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import language.
From D.pure_program_logic Require Import lifting adequacy.

From Coq Require ProofIrrelevance FunctionalExtensionality.

Module Type OLty (Import VS: VlSortsFullSig).

Include LiftWp VS.

Section olty_limit_preserving.
  Context `{Σ : gFunctors}.

  Definition envD_persistent (A : envD Σ) := ∀ ρ w, Persistent (A ρ w).

  Instance: LimitPreserving envD_persistent.
  Proof.
    apply limit_preserving_forall=> ρ; apply limit_preserving_forall=> w.
      apply bi.limit_preserving_Persistent => n ?? H. exact: H.
  Qed.

  Definition vclosed (A : envD Σ) := ∀ ρ v, A ρ v ⊢ ⌜ nclosed_vl v 0 ⌝.

  Instance: LimitPreserving vclosed.
  Proof.
    apply limit_preserving_forall=> ρ; apply limit_preserving_forall=> w.
    apply limit_preserving_entails; last apply _.
    solve_proper_ho.
  Qed.

  Definition restrict A := vclosed A ∧ envD_persistent A.
  Global Instance: LimitPreserving restrict.
  Proof.
    apply limit_preserving_and; apply _.
  Qed.
End olty_limit_preserving.

(**
"Open Logical TYpes": persistent Iris predicates over environments
and values. Adapted from
https://gitlab.mpi-sws.org/iris/examples/blob/d4f4153920ea82617c7222aeeb00b6710d51ee03/theories/logrel_heaplang/ltyping.v#L5. *)
Record olty Σ := Olty {
  olty_car : envD Σ;
  olty_v_closed : vclosed olty_car;
  olty_persistent ρ v : Persistent (olty_car ρ v);
}.
Arguments Olty {_} _%I _ {_}.
Arguments olty_car {_} _ _ _ /.
Arguments olty_v_closed {_} _ _ _ /.
Bind Scope olty_scope with olty.
Delimit Scope olty_scope with T.
Existing Instance olty_persistent.

Fail Definition testCoerce `(φ: olty Σ) ρ := φ ρ.
Definition olty2fun `(o: olty Σ) ρ := olty_car o ρ.
Coercion olty2fun: olty >-> Funclass.
Definition testCoerce `(φ: olty Σ) ρ := φ ρ.

Section olty_ofe.
  Context `{Σ : gFunctors}.
  Implicit Types (φ : envD Σ) (τ : olty Σ).

  Instance olty_equiv : Equiv (olty Σ) := λ A B, olty_car A ≡ B.
  Instance olty_dist : Dist (olty Σ) := λ n A B, olty_car A ≡{n}≡ B.
  Lemma olty_ofe_mixin : OfeMixin (olty Σ).
  Proof. by apply (iso_ofe_mixin olty_car). Qed.
  Canonical Structure oltyC := OfeT (olty Σ) olty_ofe_mixin.

  (* Only needed to define Olty using Iris fixpoints (e.g. for normal recursive types). *)
  Global Instance olty_cofe : Cofe oltyC.
  Proof.
    set curry_olty : ∀ A, restrict A → olty Σ := λ A '(conj P1 P2), @Olty Σ A P1 P2.
    apply (iso_cofe_subtype' restrict curry_olty olty_car) => //.
    - by move => [].
    - by move => ? [].
    - apply _.
  Qed.

  Global Program Instance olty_inhabited : Inhabited (olty Σ) := populate (Olty (λ _ _, False)%I _).
  Next Obligation. by unseal=>?. Qed.

  Global Instance olty_car_ne: NonExpansive (@olty_car Σ).
  Proof. by intros ??. Qed.
  Global Instance lty_car_proper : Proper ((≡) ==> (≡)) (@olty_car Σ).
  Proof. apply ne_proper, olty_car_ne. Qed.

  Program Definition pack φ (Hvc : vclosed φ) := Olty (λ ρ v, □ φ ρ v)%I _.
  Next Obligation. rewrite /vclosed; intros. iIntros "?". by iApply Hvc. Qed.

  Lemma persistently_id (P : iProp Σ) `{!Persistent P}: □P ⊣⊢ P.
  (* Proof. by iSplit; iIntros. Qed. *)
  Proof. apply: intuitionistic_intuitionistically. Qed.

  Lemma olty_car_pack_id φ (H : vclosed φ) `{∀ ρ v, Persistent (φ ρ v)} :
    olty_car (pack φ H) ≡ φ.
  Proof.
    move => ?? /=.
    apply: intuitionistic_intuitionistically.
  Qed.

  Lemma pack_olty_car_id τ : pack (olty_car τ) (olty_v_closed τ) ≡ τ.
  Proof.
    move: τ => []?????/=.
    apply: intuitionistic_intuitionistically.
  Qed.

  Global Instance ids_envD : Ids (envD Σ) := λ _, inhabitant.
  Global Instance rename_envD : Rename (envD Σ) :=
    λ r φ ρ, φ (r >>> ρ).
  Global Instance hsubst_envD : HSubst vl (envD Σ) :=
    λ sb φ ρ, φ (sb >> ρ).

  Ltac renLemmas_envD :=
    hnf; rewrite /hsubst /hsubst_envD => /= *;
    try (apply FunctionalExtensionality.functional_extensionality_dep => ?); by asimpl.

  Global Instance HSubstLemmas_envD : HSubstLemmas vl (envD Σ).
  Proof. split => //; renLemmas_envD. Qed.

  (*
    Since substitution lemmas don't use setoids,
    [HSubstLemmas vl (olty Σ)] requires proof irrelevance.
   *)

  Lemma olty_eq τ1 τ2: olty_car τ1 = olty_car τ2 → τ1 = τ2.
  Proof.
    move: τ1 τ2 => [φ1 ??] [φ2 ??]; rewrite /olty_car.
    destruct 1. f_equal; exact: ProofIrrelevance.proof_irrelevance.
  Qed.

  Global Instance ids_olty : Ids (olty Σ) := λ _, inhabitant.
  Global Program Instance rename_olty : Rename (olty Σ) :=
    λ r τ, Olty (rename r (olty_car τ)) _.
  Next Obligation. rewrite /vclosed; intros. exact: olty_v_closed. Qed.
  Global Program Instance hsubst_olty : HSubst vl (olty Σ) :=
    λ sb τ, Olty ((olty_car τ).|[sb]) (_ (olty_car τ).|[sb]).
  Next Obligation. rewrite /vclosed; intros. exact: olty_v_closed. Qed.

  Global Instance hsubstLemmas_olty : HSubstLemmas vl (olty Σ).
  Proof.
    split=> [s|??|?? s]; apply olty_eq => //; case: s => [φ??];
    rewrite /hsubst /hsubst_olty /olty_car.
    all: trivial using hsubst_id, id_hsubst, hsubst_comp.
  Qed.

(* Global Instance rename_olty2 : Rename (olty Σ) :=
    λ r τ, Olty (λ ρ, τ (r >>> ρ)) (λ ρ, olty_v_closed τ _).
  Global Instance hsubst_olty2 : HSubst vl (olty Σ) :=
    λ sb τ, Olty (λ ρ, τ (sb >> ρ)) (λ ρ, olty_v_closed τ _).
  Global Instance HSubstLemmas_olty2 : HSubstLemmas vl (olty Σ).
  Proof.
    split=> [s|??|?? s]; apply olty_eq => //; case: s => [φ??];
    (apply functional_extensionality_dep => ?);
    rewrite /hsubst /hsubst_olty2 /olty_car /=.
    all: by asimpl.
  Qed. *)

  Lemma envD_weaken ρ1 ρ2 ρ3 φ :
    φ.|[upn (length ρ1) (ren (+ length ρ2))] (to_subst (ρ1 ++ ρ2 ++ ρ3))
    = φ (to_subst (ρ1 ++ ρ3)).
  Proof. rewrite /hsubst_envD /hsubst to_subst_weaken //. Qed.

  Lemma envD_subst_up ρ1 ρ2 v φ :
    φ.|[upn (length ρ1) (v.[ren (+length ρ2)] .: ids)] (to_subst (ρ1 ++ ρ2))
    ≡ φ (to_subst (ρ1 ++ v :: ρ2)).
  Proof. rewrite /hsubst_envD /hsubst to_subst_up //. Qed.

  Lemma olty_weaken ρ1 ρ2 ρ3 τ :
    τ.|[upn (length ρ1) (ren (+ length ρ2))] (to_subst (ρ1 ++ ρ2 ++ ρ3))
    = τ (to_subst (ρ1 ++ ρ3)).
  Proof.
    (* rewrite /hsubst_olty /hsubst_envD /hsubst /= to_subst_weaken //. *)
    rewrite [@hsubst _ _ hsubst_olty]/hsubst /hsubst_olty /=.
    exact: envD_weaken.
  Qed.

  Lemma envD_weaken_one v φ ρ:
    φ.|[ren (+1)] (v .: to_subst ρ) ≡ φ (to_subst ρ).
  Proof. by rewrite (envD_weaken [] [v]). Qed.

  Lemma olty_weaken_one v τ ρ:
    τ.|[ren (+1)] (v .: to_subst ρ) ≡ τ (to_subst ρ).
  Proof. by rewrite (olty_weaken [] [v]). Qed.

  Lemma olty_subst_up ρ1 ρ2 v τ :
    τ.|[upn (length ρ1) (v.[ren (+length ρ2)] .: ids)] (to_subst (ρ1 ++ ρ2))
    ≡ τ (to_subst (ρ1 ++ v :: ρ2)).
  Proof.
    (* rewrite /hsubst_olty /hsubst_envD /hsubst /= to_subst_up //. *)
    rewrite [@hsubst _ _ hsubst_olty]/hsubst /hsubst_olty /=.
    exact: envD_subst_up.
  Qed.

  Definition sCtx := list (olty Σ).

  Fixpoint env_oltyped (Γ : sCtx) (ρ : var → vl) : iProp Σ :=
    match Γ with
    | φ :: Γ' => env_oltyped Γ' ((+1) >>> ρ) ∗ φ ρ (ρ 0)
    | nil => True
    end%I.

  Global Instance env_oltyped_persistent (Γ : sCtx) vs: Persistent (env_oltyped Γ vs).
  Proof. elim: Γ vs => [|τ Γ IHΓ] vs /=; apply _. Qed.

  Lemma env_oltyped_cl_ρ Γ ρ :
    env_oltyped Γ ρ -∗ ⌜ nclosed_sub (length Γ) 0 ρ ⌝.
  Proof.
    elim: Γ ρ => [|φ Γ IHΓ] ρ /=; [| rewrite IHΓ /olty2fun olty_v_closed ]; iIntros "!% //".
    - move => [Hclρ Hclp0] [|i /lt_S_n] Hle. exact Hclp0. apply Hclρ, Hle.
  Qed.

  Lemma env_oltyped_cl_app `{Sort X} (x : X) Γ ρ:
    env_oltyped Γ ρ -∗
    ⌜ nclosed x (length Γ) ⌝ → ⌜ nclosed x.|[ρ] 0 ⌝.
  Proof. rewrite env_oltyped_cl_ρ. iIntros "!%". exact: nclosed_sub_app. Qed.

  Lemma env_oltyped_cl_app_vl v Γ ρ:
    env_oltyped Γ ρ -∗
    ⌜ nclosed_vl v (length Γ) ⌝ → ⌜ nclosed_vl v.[ρ] 0 ⌝.
  Proof. rewrite env_oltyped_cl_ρ. iIntros "!%". exact: nclosed_sub_app_vl. Qed.

  Fixpoint env_oltyped_fin (Γ : sCtx) vs : iProp Σ :=
    match Γ, vs with
    | φ :: Γ', v :: vs => env_oltyped_fin Γ' vs ∗ φ (v .: to_subst vs) v
    | nil, nil => True
    | _, _ => False
    end%I.
  Notation "⟦ Γ ⟧*" := (env_oltyped_fin Γ).

  Global Instance env_oltyped_fin_persistent (Γ : sCtx) vs: Persistent (⟦ Γ ⟧* vs).
  Proof. elim: Γ vs => [|τ Γ IHΓ] [|v vs] /=; apply _. Qed.

  Lemma env_oltyped_transl Γ vs :
    ⟦ Γ ⟧* vs -∗ env_oltyped Γ (to_subst vs).
  Proof.
    elim: Γ vs => [|Γ φ IHΓ] [|v vs] /=;
      by [|iIntros "[]"|asimpl; rewrite IHΓ].
  Qed.

  Lemma env_oltyped_fin_cl_ρ Γ ρ:
    ⟦ Γ ⟧* ρ -∗ ⌜ nclosed_sub (length Γ) 0 (to_subst ρ) ⌝.
  Proof. rewrite env_oltyped_transl env_oltyped_cl_ρ //. Qed.

  Lemma env_oltyped_fin_cl_app `{Sort X} (x : X) Γ ρ:
    ⟦ Γ ⟧* ρ -∗
    ⌜ nclosed x (length Γ) ⌝ → ⌜ nclosed x.|[to_subst ρ] 0 ⌝.
  Proof. rewrite env_oltyped_transl env_oltyped_cl_app //. Qed.

  Lemma env_oltyped_fin_cl_app_vl v Γ ρ:
    ⟦ Γ ⟧* ρ -∗
    ⌜ nclosed_vl v (length Γ) ⌝ → ⌜ nclosed_vl v.[to_subst ρ] 0 ⌝.
  Proof. rewrite env_oltyped_transl env_oltyped_cl_app_vl //. Qed.

  Lemma interp_env_len_agree Γ ρ:
    ⟦ Γ ⟧* ρ -∗ ⌜ length ρ = length Γ ⌝.
  Proof.
    elim: Γ ρ => [|τ Γ IHΓ] [|v ρ] //=; try by iPureIntro.
    rewrite IHΓ. by iIntros "[-> _] !%".
  Qed.

  Lemma interp_env_ρ_closed Γ ρ: ⟦ Γ ⟧* ρ -∗ ⌜ cl_ρ ρ ⌝.
  Proof.
    elim: Γ ρ => [|τ Γ IHΓ] [|v ρ] //=; try by iPureIntro.
    rewrite IHΓ /olty2fun olty_v_closed. iPureIntro. intuition.
  Qed.

  Lemma interp_env_props Γ ρ:
    ⟦ Γ ⟧* ρ -∗ ⌜ cl_ρ ρ ∧ length ρ = length Γ ⌝.
  Proof.
    iIntros "#HG".
    iDestruct (interp_env_ρ_closed with "HG") as %?.
    iDestruct (interp_env_len_agree with "HG") as %?.
    by iPureIntro.
  Qed.
End olty_ofe.

Notation "⟦ Γ ⟧*" := (env_oltyped_fin Γ).
Arguments oltyC : clear implicits.

(* Different from normal TyInterp. Better? *)
Class OTyInterp ty Σ :=
  oty_interp: ty → olty Σ.
End OLty.
