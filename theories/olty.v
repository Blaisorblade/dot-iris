From D Require Import iris_prelude asubst_base asubst_intf dlang.
(* From D.pure_program_logic Require Import lifting. *)
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import language.
From D.pure_program_logic Require Import lifting adequacy.

From Coq Require ProofIrrelevance FunctionalExtensionality.

Module Type OLty (Import VS: VlSortsFullSig) (Import LVS : LiftWp VS).

Section olty_limit_preserving.
  Context `{Σ : gFunctors} {i : nat}.

  Definition hoEnvD_persistent (A : hoEnvD Σ i) := ∀ args ρ w, Persistent (A args ρ w).

  Instance: LimitPreserving hoEnvD_persistent.
  Proof.
    apply limit_preserving_forall=> args;
    apply limit_preserving_forall=> ρ; apply limit_preserving_forall=> w.
    apply bi.limit_preserving_Persistent => n f g Heq. exact: Heq.
  Qed.

  Definition vclosed (A : hoEnvD Σ i) := ∀ args ρ v, A args ρ v ⊢ ⌜ nclosed_vl v 0 ⌝.

  Instance: LimitPreserving vclosed.
  Proof.
    apply limit_preserving_forall=> args;
    apply limit_preserving_forall=> ρ; apply limit_preserving_forall=> w.
    apply limit_preserving_entails; last apply _.
    move => n f g Heq. exact: Heq.
  Qed.

  Definition restrict A := vclosed A ∧ hoEnvD_persistent A.
  Global Instance: LimitPreserving restrict.
  Proof.
    apply limit_preserving_and; apply _.
  Qed.
End olty_limit_preserving.

(**
"Open Logical TYpes": persistent Iris predicates over environments
and values. Adapted from
https://gitlab.mpi-sws.org/iris/examples/blob/d4f4153920ea82617c7222aeeb00b6710d51ee03/theories/logrel_heaplang/ltyping.v#L5. *)
Record olty Σ i := Olty {
  olty_car :> vec vl i → (var → vl) → vl → iProp Σ;
  olty_vclosed : vclosed olty_car;
  olty_persistent args ρ v : Persistent (olty_car args ρ v);
}.
Global Arguments Olty {_ _} _%I _ {_}.
Global Arguments olty_car {_ _} _ _ _ _: simpl never.
Global Arguments olty_vclosed {_ _} _ _ _.
Bind Scope olty_scope with olty.
Delimit Scope olty_scope with T.
Global Existing Instance olty_persistent.

(* Different from normal TyInterp. Better? *)
Class OTyInterp (ty : nat → Type) Σ :=
  oty_interp : ∀ {i}, ty i → olty Σ i.
(* Forces inserting coercions to -d>. *)
Notation oApp := (olty_car : olty _ _ → hoEnvD _ _).

Local Definition testCoerce `(τ : olty Σ 0) := vclose (oApp τ).

Section olty_ofe.
  Context `{Σ : gFunctors} {i : nat}.
  Implicit Types (φ : hoEnvD Σ i) (τ : olty Σ i).

  Instance olty_equiv : Equiv (olty Σ i) := λ A B, oApp A ≡ B.
  Instance olty_dist : Dist (olty Σ i) := λ n A B, oApp A ≡{n}≡ B.
  Lemma olty_ofe_mixin : OfeMixin (olty Σ i).
  Proof. by apply (iso_ofe_mixin oApp). Qed.
  Canonical Structure oltyO := OfeT (olty Σ i) olty_ofe_mixin.

  (* Only needed to define Olty using Iris fixpoints (e.g. for normal recursive types). *)
  Global Instance olty_cofe : Cofe oltyO.
  Proof.
    set curry_olty : ∀ A, restrict A → olty Σ i := λ A '(conj P1 P2), @Olty Σ i A P1 P2.
    apply (iso_cofe_subtype' restrict curry_olty olty_car) => //.
    - by move => [].
    - by move => ? [].
    - apply _.
  Qed.

  Global Program Instance olty_inhabited : Inhabited (olty Σ i) := populate (Olty (λ _ _ _, False)%I _).
  Next Obligation. by unseal=>?. Qed.

  Global Instance olty_car_ne : NonExpansive oApp.
  Proof. intros n f g Heq. apply Heq. Qed.
  Global Instance lty_car_proper : Proper ((≡) ==> (≡)) oApp.
  Proof. apply ne_proper, olty_car_ne. Qed.

  Program Definition pack φ (Hvc : vclosed φ) := Olty (λ args ρ v, □ φ args ρ v)%I _.
  Next Obligation. rewrite /vclosed; intros. iIntros "?". by iApply Hvc. Qed.

  Lemma persistently_id (P : iProp Σ) `{!Persistent P}: □P ⊣⊢ P.
  (* Proof. by iSplit; iIntros. Qed. *)
  Proof. apply: intuitionistic_intuitionistically. Qed.

  Lemma olty_car_pack_id φ (H : vclosed φ) `{∀ args ρ v, Persistent (φ args ρ v)} :
    oApp (pack φ H) ≡ φ.
  Proof.
    move => ??? /=.
    apply: intuitionistic_intuitionistically.
  Qed.

  Lemma pack_olty_car_id τ : pack (olty_car τ) (olty_vclosed τ) ≡ τ.
  Proof.
    move: τ => [τ Hp Hvc] args ρ v; rewrite /olty_car/=.
    apply: intuitionistic_intuitionistically.
  Qed.

  Global Instance ids_hoEnvD : Ids (hoEnvD Σ i) := λ _, inhabitant.
  Global Instance rename_hoEnvD : Rename (hoEnvD Σ i) :=
    λ r φ args ρ, φ args (r >>> ρ).
  Global Instance hsubst_hoEnvD : HSubst vl (hoEnvD Σ i) :=
    λ sb φ args ρ, φ args (sb >> ρ).

  Ltac renLemmas_hoEnvD :=
    hnf; rewrite /hsubst /hsubst_hoEnvD => /= *;
    do 2 (apply FunctionalExtensionality.functional_extensionality_dep => ?); by asimpl.

  Global Instance HSubstLemmas_hoEnvD : HSubstLemmas vl (hoEnvD Σ i).
  Proof. split => //; renLemmas_hoEnvD. Qed.

  (*
    Since substitution lemmas don't use setoids,
    [HSubstLemmas vl (olty Σ)] requires proof irrelevance.
   *)

  Lemma olty_eq τ1 τ2: olty_car τ1 = olty_car τ2 → τ1 = τ2.
  Proof.
    move: τ1 τ2 => [φ1 Hp1 Hvc1] [φ2 Hp2 Hvc2]. rewrite /olty_car /=.
    intros ->. f_equal; exact: ProofIrrelevance.proof_irrelevance.
  Qed.

  Global Instance ids_olty : Ids (olty Σ i) := λ _, inhabitant.
  Global Program Instance rename_olty : Rename (olty Σ i) :=
    λ r τ, Olty (rename r (olty_car τ)) _.
  Next Obligation. rewrite /vclosed; intros. exact: olty_vclosed. Qed.
  Global Program Instance hsubst_olty : HSubst vl (olty Σ i) :=
    λ sb τ, Olty ((olty_car τ).|[sb]) (_ (olty_car τ).|[sb]).
  Next Obligation. rewrite /vclosed; intros. exact: olty_vclosed. Qed.

  Global Instance hsubstLemmas_olty : HSubstLemmas vl (olty Σ i).
  Proof.
    split=> [s|??|?? s]; apply olty_eq => //; case: s => [φ??];
    rewrite /hsubst /hsubst_olty /olty_car.
    all: trivial using hsubst_id, id_hsubst, hsubst_comp.
  Qed.

(* Global Instance rename_olty2 : Rename (olty Σ i) :=
    λ r τ, Olty (λ ρ, τ (r >>> ρ)) (λ ρ, olty_vclosed τ _).
  Global Instance hsubst_olty2 : HSubst vl (olty Σ i) :=
    λ sb τ, Olty (λ ρ, τ (sb >> ρ)) (λ ρ, olty_vclosed τ _).
  Global Instance HSubstLemmas_olty2 : HSubstLemmas vl (olty Σ i).
  Proof.
    split=> [s|??|?? s]; apply olty_eq => //; case: s => [φ??];
    (apply functional_extensionality_dep => ?);
    rewrite /hsubst /hsubst_olty2 /olty_car /=.
    all: by asimpl.
  Qed. *)

  Lemma hoEnvD_weaken ρ1 ρ2 ρ3 φ args :
    φ.|[upn (length ρ1) (ren (+ length ρ2))] args (to_subst (ρ1 ++ ρ2 ++ ρ3))
    = φ args (to_subst (ρ1 ++ ρ3)).
  Proof. rewrite /hsubst_hoEnvD /hsubst to_subst_weaken //. Qed.

  Lemma olty_weaken ρ1 ρ2 ρ3 τ args :
    τ.|[upn (length ρ1) (ren (+ length ρ2))] args (to_subst (ρ1 ++ ρ2 ++ ρ3))
    = τ args (to_subst (ρ1 ++ ρ3)).
  Proof.
    (* rewrite /hsubst_olty /hsubst_hoEnvD /hsubst /= to_subst_weaken //. *)
    rewrite [@hsubst _ _ hsubst_olty]/hsubst /hsubst_olty /=.
    exact: hoEnvD_weaken.
  Qed.

  Lemma hoEnvD_weaken_one v φ ρ args :
    φ.|[ren (+1)] args (v .: to_subst ρ) = φ args (to_subst ρ).
  Proof. by rewrite (hoEnvD_weaken [] [v]). Qed.

  Lemma olty_weaken_one v τ ρ args :
    oApp τ.|[ren (+1)] args (v .: to_subst ρ) ≡ τ args (to_subst ρ).
  Proof. by rewrite (olty_weaken [] [v]). Qed.
End olty_ofe.

Notation oClose φ := (olty_car φ vnil : envD _).
Section olty_ofe_2.
  Context `{Σ : gFunctors} {i : nat}.
  Implicit Types (φ : hoEnvD Σ i) (τ : olty Σ i).

  Definition sCtx := list (olty Σ 0).

  Fixpoint env_oltyped (Γ : sCtx) (ρ : var → vl) : iProp Σ :=
    match Γ with
    | φ :: Γ' => env_oltyped Γ' ((+1) >>> ρ) ∗ oClose φ ρ (ρ 0)
    | nil => True
    end%I.

  Global Instance env_oltyped_persistent (Γ : sCtx) ρ: Persistent (env_oltyped Γ ρ).
  Proof. elim: Γ ρ => [|τ Γ IHΓ] ρ /=; apply _. Qed.

  Lemma env_oltyped_cl_ρ Γ ρ :
    env_oltyped Γ ρ -∗ ⌜ nclosed_sub (length Γ) 0 ρ ⌝.
  Proof.
    elim: Γ ρ => [|φ Γ IHΓ] ρ /=; [| rewrite IHΓ olty_vclosed ]; iIntros "!% //".
    - move => [Hclρ Hclp0] [|n /lt_S_n] Hle. exact Hclp0. apply Hclρ, Hle.
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
    | φ :: Γ', v :: vs => env_oltyped_fin Γ' vs ∗ oClose φ (v .: to_subst vs) v
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
      by [ | iIntros "[]"| asimpl; rewrite IHΓ ].
  Qed.

  Lemma env_oltyped_fin_cl_ρ Γ ρ:
    ⟦ Γ ⟧* ρ -∗ ⌜ nclosed_sub (length Γ) 0 (to_subst ρ) ⌝.
  Proof. rewrite env_oltyped_transl env_oltyped_cl_ρ //. Qed.

  Lemma env_oltyped_fin_cl_app `{Sort X} (x : X) Γ ρ:
    ⟦ Γ ⟧* ρ -∗
    ⌜ nclosed x (length Γ) ⌝ → ⌜ nclosed x.|[to_subst ρ] 0 ⌝.
  Proof. rewrite env_oltyped_transl (env_oltyped_cl_app x) //. Qed.

  Lemma env_oltyped_fin_cl_app_vl v Γ ρ:
    ⟦ Γ ⟧* ρ -∗
    ⌜ nclosed_vl v (length Γ) ⌝ → ⌜ nclosed_vl v.[to_subst ρ] 0 ⌝.
  Proof. rewrite env_oltyped_transl env_oltyped_cl_app_vl //. Qed.

  Lemma interp_env_ρ_closed Γ ρ: ⟦ Γ ⟧* ρ -∗ ⌜ cl_ρ ρ ⌝.
  Proof.
    elim: Γ ρ => [|τ Γ IHΓ] [|v ρ] //=; try by iIntros "!%".
    rewrite IHΓ olty_vclosed. iIntros "!%". intuition.
  Qed.

  Lemma interp_env_lookup Γ ρ (τ : olty Σ 0) x:
    Γ !! x = Some τ →
    ⟦ Γ ⟧* ρ -∗ oClose τ.|[ren (+x)] (to_subst ρ) (to_subst ρ x).
  Proof.
    elim: Γ ρ x => [//|τ' Γ' IHΓ] [|v ρ] x Hx /=. by iIntros "[]".
    iDestruct 1 as "[Hg Hv]". move: x Hx => [ [->] | x Hx] /=.
    - rewrite hsubst_id. by [].
    - rewrite hrenS.
      iApply (olty_weaken_one v (τ.|[ren (+x)]) ρ).
      iApply (IHΓ ρ x Hx with "Hg").
  Qed.

  Program Definition ho_closed_olty {i} (φ : hoEnvD Σ i) `{∀ args ρ v, Persistent (φ args ρ v)} : olty Σ i :=
    Olty (λ args ρ v, ⌜ nclosed_vl v 0 ⌝ ∗ φ args ρ v)%I _.
  Next Obligation. iIntros (??????) "[$_]". Qed.

  Definition closed_olty (φ : envD Σ)`{∀ ρ v, Persistent (φ ρ v)} : olty Σ 0 :=
    ho_closed_olty (vopen φ).

  (** We can define once and for all basic "logical" types: top, bottom, and, or, later and μ. *)
  Definition oTop : olty Σ i := ho_closed_olty (λ args ρ v, True)%I.

  Program Definition oBot : olty Σ i := Olty (λ args ρ v, False)%I _.
  Next Obligation. intros **?**. exact: False_elim. Qed.

  Program Definition oAnd τ1 τ2 : olty Σ i := Olty (λ args ρ v, τ1 args ρ v ∧ τ2 args ρ v)%I _.
  Next Obligation. intros **?**. rewrite olty_vclosed. iIntros "[$ _]". Qed.

  Program Definition oOr τ1 τ2 : olty Σ i := Olty (λ args ρ v, τ1 args ρ v ∨ τ2 args ρ v)%I _.
  Next Obligation. intros **?**. rewrite !olty_vclosed. iIntros "[$ | $]". Qed.

  Definition eLater n (φ : hoEnvD Σ i) : hoEnvD Σ i := (λ args ρ v, ▷^n φ args ρ v)%I.
  Definition oLater τ := ho_closed_olty (eLater 1 τ).

  Program Definition ho_oMu {i} (τ : olty Σ i) : olty Σ i := Olty (λ args ρ v, τ args (v .: ρ) v) _.
  Next Obligation. rewrite /vclosed; intros. exact: olty_vclosed. Qed.

  Definition oMu (τ : olty Σ 0) : olty Σ 0 := ho_oMu τ.

  Lemma interp_TMu_ren (T : olty Σ i) args ρ v: ho_oMu T.|[ren (+1)] args (to_subst ρ) v ≡ T args (to_subst ρ) v.
  Proof. rewrite [_ (ho_oMu _)]/olty_car /= (olty_weaken_one v T ρ args v). by []. Qed.

  Definition interp_expr `{dlangG Σ} (φ : hoEnvD Σ 0) : envPred tm Σ :=
    λ ρ t, WP t {{ vclose φ ρ }} %I.
  Global Arguments interp_expr /.

  Definition oTSel0 `{dlangG Σ} s σ :=
    closed_olty (λ ρ v, ∃ ψ, s ↗[ σ ] ψ ∧ ▷ □ ψ v)%I.
End olty_ofe_2.

Notation "⟦ Γ ⟧*" := (env_oltyped_fin Γ).
Arguments oltyO : clear implicits.
End OLty.

Module Type OLtyJudgements (Import VS: VlSortsFullSig) (Import LVS : LiftWp VS).
Include OLty VS LVS.
Section judgments.
  Context `{dlangG Σ}.
  Implicit Types (τ : olty Σ 0).

  Definition step_indexed_ivstp Γ τ1 τ2 i j: iProp Σ :=
    (□∀ ρ v, ⌜ nclosed_vl v 0 ⌝ →
      ⟦Γ⟧*ρ → (▷^i oClose τ1 (to_subst ρ) v) → ▷^j oClose τ2 (to_subst ρ) v)%I.
  Global Arguments step_indexed_ivstp /.

  Definition ietp Γ τ e : iProp Σ := (⌜ nclosed e (length Γ) ⌝ ∗
    □∀ ρ, ⟦Γ⟧* ρ → interp_expr τ (to_subst ρ) (e.|[to_subst ρ]))%I.
  Global Arguments ietp /.

  Definition step_indexed_ietp Γ τ e i: iProp Σ :=
    (⌜ nclosed e (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ →
      interp_expr (eLater i τ) (to_subst ρ) (e.|[to_subst ρ]))%I.
  Global Arguments step_indexed_ietp /.

End judgments.

Notation "Γ ⊨ e : τ" := (ietp Γ τ e) (at level 74, e, τ at next level).
Notation "Γ ⊨ e : τ , i" := (step_indexed_ietp Γ τ e i) (at level 74, e, τ at next level).
Notation "Γ ⊨ [ τ1 , i ]  <: [ τ2 , j ]" := (step_indexed_ivstp Γ τ1 τ2 i j) (at level 74, τ1, τ2 at next level).

Section typing.
  Context `{dlangG Σ}.
  Implicit Types (τ : olty Σ 0).

  Lemma iterate_TLater_later i τ ρ v:
    nclosed_vl v 0 →
    oClose (iterate oLater i τ) ρ v ≡ (vclose (eLater i τ) ρ v).
  Proof.
    elim: i => [|i IHi] // => Hcl. rewrite iterate_S [_ ρ]/olty_car/= /eLater IHi //.
    iSplit; by [iIntros "#[_ $]" | iIntros "$"].
  Qed.

  Lemma T_Var Γ x τ:
    Γ !! x = Some τ →
    (*──────────────────────*)
    Γ ⊨ of_val (ids x) : τ.|[ren (+x)].
  Proof.
    iIntros (Hx) "/=". iSplit. eauto using lookup_fv.
    iIntros "!>" (vs) "#Hg". rewrite hsubst_of_val -wp_value' interp_env_lookup // id_subst. by [].
  Qed.

  Lemma andstp1 Γ τ1 τ2 i : Γ ⊨ [oAnd τ1 τ2 , i] <: [τ1 , i].
  Proof. iIntros "!>" (???) "#Hg #[$ _]". Qed.

  Lemma andstp2 Γ τ1 τ2 i : Γ ⊨ [oAnd τ1 τ2 , i] <: [τ2 , i].
  Proof. iIntros "!>" (???) "#Hg #[_ $]". Qed.
End typing.

End OLtyJudgements.
