From D Require Import tactics proofmode_extra.
(* From D.pure_program_logic Require Import lifting. *)
From iris.base_logic Require Import lib.iprop.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import language.
From D.pure_program_logic Require Import lifting adequacy.
From D Require Export gen_iheap saved_interp.
Require Import Program.
Import uPred.

From D Require Import prelude iris_prelude asubst_base asubst_intf dlang.
From Coq Require ProofIrrelevance.

Module Type SortsIntf2 (values: Values).
Import values.
Include (SortsIntf values).
End SortsIntf2.

Module OLty (values: Values) (sorts: SortsIntf values).
Import values sorts.
(* Test that this interface works. *)
(* Module M <: SortsIntf2 values := SortsLemmas values. *)
(* Include SortsLemmas values. *)

Notation envD Σ := ((var -> vl) -d> vl -d> iProp Σ).

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

  Program Definition pack φ (H : vclosed φ) := Olty (λ ρ v, □ φ ρ v)%I _.
  Next Obligation. iIntros (??) "H". by iApply H. Qed.

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
    try (apply functional_extensionality_dep => ?); by asimpl.

  Global Instance HSubstLemmas_envD : HSubstLemmas vl (envD Σ).
  Proof.
    split => //; renLemmas_envD.
  Qed.

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
  Next Obligation. move=>??. exact: olty_v_closed. Qed.
  Global Program Instance hsubst_olty : HSubst vl (olty Σ) :=
    λ sb τ, Olty ((olty_car τ).|[sb]) (_ (olty_car τ).|[sb]).
  Next Obligation. move=>??. exact: olty_v_closed. Qed.

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

  Lemma olty_subst_up ρ1 ρ2 v τ :
    τ.|[upn (length ρ1) (v.[ren (+length ρ2)] .: ids)] (to_subst (ρ1 ++ ρ2))
    ≡ τ (to_subst (ρ1 ++ v :: ρ2)).
  Proof.
    (* rewrite /hsubst_olty /hsubst_envD /hsubst /= to_subst_up //. *)
    rewrite [@hsubst _ _ hsubst_olty]/hsubst /hsubst_olty /=.
    exact: envD_subst_up.
  Qed.
End olty_ofe.
Arguments oltyC : clear implicits.

(* Different from normal TyInterp. Better? *)
Class OTyInterp ty Σ :=
  oty_interp: ty → olty Σ.
End OLty.
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

Module OLty_judge (values: Values) (sorts: SortsIntf values).
Import values sorts.
(* TODO Eventually switch to: *)

(* Include (LiftWp values sorts). *)
(* Or just inline this code there. *)
Module M := LiftWp values sorts.
Import M.

Include OLty values sorts.

Class Closeable s := nclosed_s : s → nat → Prop.
Instance closeable_sort s `{Sort s} : Closeable s := nclosed.
Instance closeable_vl : Closeable vl := nclosed_vl.

Definition env := var -> vl.

Implicit Types (v: vl) (vs : vls) (ρ : env).
Implicit Types (Σ : gFunctors).

Definition test_interp_expr2 `{dlangG Σ} (φ : olty Σ) :=
  λ ρ t, WP t {{ φ ρ }} %I.

Section judgments.
Context `{dlangG Σ} `{OTyInterp ty Σ}.

Notation sCtx := (list (olty Σ)).
Notation ctx := (list ty).

Notation "⟦ T ⟧" := (oty_interp T).

Fixpoint env_oltyped' (Γ : sCtx) (ρ : var → vl) : iProp Σ :=
  match Γ with
  | φ :: Γ' => env_oltyped' Γ' ((+1) >>> ρ) ∗ φ ρ (ρ 0)
  | nil => True
  end%I.

Lemma env_oltyped_cl_ρ Γ ρ:
  env_oltyped' Γ ρ -∗ ⌜ nclosed_sub (length Γ) 0 ρ ⌝.
Proof.
  elim: Γ ρ => [|φ Γ IHΓ] ρ /=. by iIntros "!%" (???); lia.
  rewrite IHΓ; iDestruct 1 as (Hf) "Hρ0"; iIntros ([|i] Hle).
  - by iApply olty_v_closed.
  - iIntros "!%". apply Hf. lia.
Qed.

Lemma env_oltyped_cl_app `{Sort X} (x : X) Γ ρ:
  env_oltyped' Γ ρ -∗
  ⌜ nclosed x (length Γ) ⌝ → ⌜ nclosed x.|[ρ] 0 ⌝.
Proof.
  rewrite env_oltyped_cl_ρ. iIntros "!%".
  exact: nclosed_sub_app.
Qed.

Lemma env_oltyped_cl_app_vl v Γ ρ:
  env_oltyped' Γ ρ -∗
  ⌜ nclosed_vl v (length Γ) ⌝ → ⌜ nclosed_vl v.[ρ] 0 ⌝.
Proof.
  rewrite env_oltyped_cl_ρ. iIntros "!%".
  exact: nclosed_sub_app_vl.
Qed.

Fixpoint env_oltyped (Γ : sCtx) vs : iProp Σ :=
  match Γ, vs with
  | φ :: Γ', v :: vs => env_oltyped Γ' vs ∗ φ (v .: to_subst vs) v
  | nil, nil => True
  | _, _ => False
  end%I.
Instance env_oltyped_persistent (Γ : sCtx) vs: Persistent (env_oltyped Γ vs).
Proof. elim: Γ vs => [|τ Γ IHΓ] [|v vs] /=; apply _. Qed.

Lemma env_oltyped_transl Γ vs :
  env_oltyped Γ vs -∗ env_oltyped' Γ (to_subst vs).
Proof.
  elim: Γ vs => [|Γ φ IHΓ] [|v vs] /=;
    by [|iIntros "[]"|asimpl; rewrite IHΓ].
Qed.

Definition oty_interp_env (Γ : ctx) : sCtx := map oty_interp Γ.
Definition env_typed (Γ : ctx) : vls -d> iProp Σ := env_oltyped (oty_interp_env Γ).

Instance env_typed_persistent `{OTyInterp ty Σ} Γ vs : Persistent (env_typed Γ vs) := env_oltyped_persistent _ _.

Definition judgment Σ s : Type := option s * (env -d> option s -d> iProp Σ).
Definition nosubj_judgment Σ : Type := env -d> iProp Σ.
Definition subj_judgment Σ s : Type := s * (env -d> s -d> iProp Σ).
Program Definition subj_judgment_to_judgment {Σ s} : subj_judgment Σ s → judgment Σ s :=
  λ '(x, φ), (Some x, λ ρ, from_option (φ ρ) False)%I.

Definition judgment_holds `{Closeable s} (Γ : sCtx) (J : judgment Σ s): iProp Σ :=
  (⌜ from_option (flip nclosed_s (length Γ)) True (fst J) ⌝ ∗ □∀ vs, env_oltyped Γ vs → (snd J) (to_subst vs) (fst J))%I.
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
    (□∀ vs v, ⌜ nclosed_vl v 0 ⌝ → env_oltyped Γ vs →
      (▷^i1 φ1 (to_subst vs) v) → ▷^i2 φ2 (to_subst vs) v)%I.
Proof.
  iSplit; [iIntros "#[_ H] /= !>" (???) "#?" |
    iIntros "#H"; iSplit; first done; iIntros "!>" (?) "#? /="; iIntros (??)].
  all: by iApply "H".
Qed.
Program Definition oAnd φ1 φ2 : olty Σ := Olty (λ ρ v, φ1 ρ v ∧ φ2 ρ v)%I _.
Next Obligation. iIntros (??) "#[H _]". by iApply olty_v_closed. Qed.

Program Definition oOr φ1 φ2 : olty Σ := Olty (λ ρ v, φ1 ρ v ∨ φ2 ρ v)%I _.
Next Obligation. iIntros (??) "#[H | H]"; by iApply olty_v_closed. Qed.

Lemma andstp1 Γ φ1 φ2 i : (Γ ⊨ [oAnd φ1 φ2 , i] <: [φ1 , i]).
Proof.
  rewrite equiv_vstp /=. by iIntros "!>" (???) "#Hg #[? ?]".
Qed.
End judgments.

End OLty_judge.
