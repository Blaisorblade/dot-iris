From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
From D Require Import prelude iris_prelude saved_interp_n.
Import uPred.

Unset Program Cases.
(* Repeat temporarily-disabled Iris notations. *)
Notation "{ x  &  P }" := (sigTOF (λ x, P%OF)) : oFunctor_scope.
Notation "{ x : A &  P }" := (@sigTOF A%type (λ x, P%OF)) : oFunctor_scope.

Module try1.
Section saved_pred3_use.
  Context {vl : Type} {Σ : gFunctors}.

  Notation envD Σ := ((var → vl) -d> vl -d> iProp Σ).
  Notation hoEnvD Σ := (list vl -d> envD Σ).
  Implicit Types (Φ : hoEnvD Σ) (n : nat).
  Definition eFalse : envD Σ := λ ρ v, False%I.

  (* We can track function arity by just storing a number,
     but that's a bit cumbersome. *)
  Definition hoEnvND Σ : Type := nat * hoEnvD Σ.
  Definition beta : hoEnvND Σ → vl → hoEnvND Σ := λ '(n, Φ) a,
    match n with
    | 0 => (0, λ _, eFalse)
    | S n => (n, λ args, Φ (a :: args))
    end%I.
  Definition close : hoEnvND Σ → envD Σ := λ '(n, Φ), Φ [].
  Definition lambda n (Φ : vl → hoEnvD Σ) : hoEnvND Σ :=
    (n + 1, λ args,
      match args with
      | w :: args => Φ w args
      | [] => eFalse
      end%I).
End saved_pred3_use.
End try1.

Module try2.

Definition vec n vl := fin n → vl.
Section vec.
  Context {vl : Type}.
  (* vector operations, on a functional representation of vectors. *)
  Definition vcons {n} (v : vl) (args: vec n vl) : fin (S n) → vl :=
    λ i,
      match i in fin (S n0) with
      | Fin.F1 => λ _, v
      | Fin.FS i' => λ args', args' i'
      end args.

  Definition emptyArgs : vec 0 vl := Fin.case0 _.
  Definition vhead {n} (args: vec (S n) vl) : vl := args Fin.F1.
  Definition vtail {n} (args: vec (S n) vl) : fin n → vl :=
    λ i, args (Fin.FS i).
End vec.

(* To prove saved_pred3_own_contractive, below, we need to hide n under ▶. *)
Definition mFun vl : oFunctor := { n & vec n vl -d> (var → vl) -d> vl -d> ▶ ∙ }.
Notation savedPred3G Σ vl := (savedAnythingG Σ (mFun vl)).
Notation savedPred3Σ vl := (savedAnythingΣ (mFun vl)).
From D Require Import asubst_intf dlang olty.

Module Foo (values: Values) (sorts: SortsIntf values).
  Module M := (OLty values sorts).
  Module N := LiftWp values sorts.
  Import M N values.
  Notation envD Σ := ((var → vl) -d> vl -d> iProp Σ).
  Notation hoEnvND n Σ := (vec n vl -d> envD Σ).

Section saved_pred3.
  Import EqNotations.

  (* For Iris. *)

  Global Instance projT1_ne {A P}: NonExpansive (projT1: @sigTO A P → leibnizO A).
  Proof. solve_proper. Qed.

  Lemma projT2_ne {A P}: ∀ n (x1 x2 : @sigTO A P) (Heq : x1 ≡{n}≡ x2),
    rew (sigT_dist_proj1 n Heq) in projT2 x1 ≡{n}≡ projT2 x2.
  Proof. by destruct Heq. Qed.

  Context `{!savedPred3G Σ vl}.

  Definition hoEnvD_P Σ := (λ n, hoEnvND n Σ).
  Definition hoEnvDO Σ : ofeT := sigTO (hoEnvD_P Σ).

  Definition packedFun : ofeT := mFun vl (iProp Σ) uPred_cofe.
  Definition packedFun_eq : packedFun =
    sigTO (λ n, vec n vl -d> (var → vl) -d> vl -d> laterO (iProp Σ)) := reflexivity _.

  Definition packedFun_arity : packedFun -n> natO := λne x, projT1 x.

  Implicit Types (Ψ : packedFun).

  (* Manipulate *)
  Definition close {A} (Φ : vec 0 vl -d> A): A := Φ emptyArgs.

  Definition beta {n A} (Φ : vec (S n) vl -d> A) v : vec n vl -d> A :=
    λ args, Φ (vcons v args).

  Definition lambda {n A} (Φ : vl → vec n vl -d> A) : vec (S n) vl -d> A :=
    λ args, Φ (vhead args) (vtail args).

  (* Right definition? *)
  Definition subtype {n} (φ1 φ2 : hoEnvND n Σ) ρ : iProp Σ :=
    (∀ (args : vec n vl) v, φ1 args ρ v -∗ φ2 args ρ v)%I.

  Fixpoint subtype_w_expKind ρ n :
      ∀ (φ1 φ2 : hoEnvND n Σ) (argTs : vec n (envD Σ)), iProp Σ :=
    match n with
    | 0 =>   λ φ1 φ2 argTs,
        ∀ v, close φ1 ρ v -∗ close φ2 ρ v
    | S n => λ φ1 φ2 argTs,
        ∀ v, vhead argTs ρ v -∗
          subtype_w_expKind ρ n (beta φ1 v) (beta φ2 v) (vtail argTs)
    end%I.

  Definition cpack n : hoEnvND n Σ → packedFun :=
    λ Φf, existT n (λ args ρ v, Next (Φf args ρ v)).

  Global Instance cpack_contractive: Contractive (cpack n).
  Proof.
    rewrite /cpack => ?????.
    apply (existT_ne _ eq_refl).
    solve_contractive_ho.
  Qed.
  Program Definition pack : hoEnvDO Σ -n> packedFun :=
    λne '(existT n Φ), cpack n Φ.
  Next Obligation.
    move => ?[??][??][/= Heq ?]. destruct Heq. by f_equiv.
  Qed.

  Definition saved_pred3_own γ i (Φ : hoEnvND i Σ) : iProp Σ :=
    saved_anything_own (F := mFun vl) γ (pack (existT i Φ)).

  Notation "γ ⤇[ i  ] φ" := (saved_pred3_own γ i φ) (at level 20).

  Instance saved_pred3_own_contractive γ i : Contractive (saved_pred3_own γ i).
  Proof.
    rewrite /saved_pred3_own => n f g /= Heq. f_equiv.
    apply (existT_ne _ eq_refl) => ??? /=.
    solve_contractive_ho.
  Qed.

  Lemma saved_pred3_alloc i φ : (|==> ∃ γ, γ ⤇[ i ] φ)%I.
  Proof. apply saved_anything_alloc. Qed.

  Lemma same_arity_1 {Φ Ψ : packedFun} {n} :
    Φ ≡{n}≡ Ψ → packedFun_arity Φ = packedFun_arity Ψ.
  Proof. destruct Φ, Ψ. by case. Qed.

  Lemma same_arity Ψ1 Ψ2 : Ψ1 ≡ Ψ2 -∗
    ⌜ packedFun_arity Ψ1 = packedFun_arity Ψ2 ⌝: iProp Σ.
  Proof. rewrite /= sigT_equivI. by iDestruct 1 as (Heq) "_". Qed.

  Lemma saved_pred3_agree_arity γ {i j Φ1 Φ2}:
    γ ⤇[ i ] Φ1 -∗ γ ⤇[ j ] Φ2 -∗ ⌜ i = j ⌝.
  Proof.
    iIntros "HΦ1 HΦ2 /=".
    iDestruct (saved_anything_agree with "HΦ1 HΦ2") as "Heq".
    by rewrite same_arity.
  Qed.

  Lemma saved_pred3_agree γ i (Φ1 Φ2 : hoEnvND i Σ) a b c:
    γ ⤇[ i ] Φ1 -∗ γ ⤇[ i ] Φ2 -∗ ▷ (Φ1 a b c ≡ Φ2 a b c).
  Proof.
    iIntros "HΦ1 HΦ2 /=".
    iDestruct (saved_anything_agree with "HΦ1 HΦ2") as "Heq".
    rewrite /= sigT_equivI. iDestruct "Heq" as (Heq) "Heq".
    rewrite (proof_irrel Heq eq_refl) /=.
    repeat setoid_rewrite bi.discrete_fun_equivI; iNext.
    iApply "Heq".
  Qed.

  Lemma saved_pred3_agree_dep γ {i j Φ1 Φ2} a b c:
    γ ⤇[ i ] Φ1 -∗ γ ⤇[ j ] Φ2 -∗ ∃ eq : i = j,
    ▷ ((rew [hoEnvD_P Σ] eq in Φ1) a b c ≡ Φ2 a b c).
  Proof.
    iIntros "HΦ1 HΦ2 /=".
    iDestruct (saved_pred3_agree_arity with "HΦ1 HΦ2") as %->.
    iExists eq_refl; cbn.
    iApply (saved_pred3_agree with "HΦ1 HΦ2").
  Qed.

  Definition unpack :
    ∀ Ψ, hoEnvND (packedFun_arity Ψ) Σ :=
    λ '(existT n Φ), (λ args ρ v,
      let '(Next f) := (Φ args ρ v) in f)%I.

  Lemma pred_impl (Φ Ψ : packedFun) n (Heq: Φ ≡{n}≡ Ψ)
    (a : vec (packedFun_arity Φ) vl) b c:
    Next (unpack Φ a b c) ≡{n}≡ Next (unpack Ψ (rew [λ n, vec n vl] (same_arity_1 Heq) in a) b c).
  Proof.
    move: (same_arity_1 Heq) => HeqN. destruct Φ, Ψ; simpl in *.
    case: Heq => /= Heq1.
    have {HeqN} ->: HeqN = Heq1. exact: proof_irrel.
    destruct Heq1; cbn => H. exact: H.
  Qed.
  Notation "s ↝[ i ] φ" := (∃ γ, (s ↦ γ) ∗ (γ ⤇[ i ] φ))%I  (at level 20) : bi_scope.

End saved_pred3.

Opaque saved_pred3_own.

Notation "γ ⤇[ i ] φ" := (saved_pred3_own γ i φ) (at level 20).
Notation "s ↝[ i ] φ" := (∃ γ, (s ↦ γ) ∗ (γ ⤇[ i ] φ))%I  (at level 20) : bi_scope.

End Foo.
From D.Dot Require Import syn unary_lr.
Include Foo syn syn.

Section bar.
  Context `{!savedPred3G Σ vl} `{!N.dlangG Σ}.
  (* Implicit Types (interp : envD Σ) (φ : D). *)
About saved_pred3_own.

  Definition hoD n Σ := vec n vl -d> vl -d> iProp Σ.

  Definition idm_proj_semtype (d : dm) n (φ : hoD n Σ) : iProp Σ :=
    (∃ s σ interp,
      s ↝[ n ] interp ∗
      ⌜ d = dtysem σ s
       ∧ φ = λ args v, interp args (to_subst σ) v ⌝)%I.
  Global Arguments idm_proj_semtype: simpl never.
  Notation "d ↗[ n ] φ" := (idm_proj_semtype d n φ) (at level 20).

  Notation envPred s := (vls -d> s -d> iProp Σ).
  Definition subtype' {n} i j (φ1 φ2 : hoD n Σ) : iProp Σ :=
    (□∀ (args : vec n vl) v, ⌜ nclosed_vl v 0 ⌝ → ▷^i φ1 args v -∗ ▷^j φ2 args v)%I.
  Definition semEquiv {n} i j (φ1 φ2 : hoD n Σ) : iProp Σ :=
    (□∀ (args : vec n vl) v, ⌜ nclosed_vl v 0 ⌝ → ▷^i φ1 args v ∗-∗ ▷^j φ2 args v)%I.

  Definition kind n Σ := hoD n Σ → iProp Σ.

  (* The point of Sandro's kind syntax is to use this only at kind 0. *)
  (* Definition ktmem {n} (φ1 φ2 : hoD n Σ) φ :=
    (subtype' n 1 1 φ1 φ ∗ subtype' n 1 1 φ φ)%I. *)
  Definition ktmem (φ1 φ2 : hoD 0 Σ) φ :=
    (subtype' 1 1 φ1 φ ∗ subtype' 1 1 φ φ)%I.

  Definition kpi {n} (K : kind n Σ) (φ₁ : hoD 0 Σ) : kind (S n) Σ :=
    λ φ, (□∀ arg, close φ₁ arg → K (beta φ arg))%I.

  Definition def_interp_tmem {n} : kind n Σ → envPred dm :=
    λ K ρ d, (∃ φ, d ↗[ n ] φ ∗ K φ)%I.
  Definition def_interp_tmem_spec (φ1 φ2 : hoD 0 Σ) : envPred dm :=
    def_interp_tmem (ktmem φ1 φ2).
  (* Olty needed. Also, without using Olty, we can't use the fact that v is closed in a subtyping proof.
    *)
  (*
    A possible sketch of subtyping for lambdas? Not quite working...
    It's good, but we can't use to compare the various subtyping rules
    for lambdas. Also because my lambdas are total and work
    on arbitrary arguments — they might, at best, become False on bad
    ones. *)
  Definition lam_subtype {n} (argT : hoD 0 Σ) (φ1 φ2 : hoD (S n) Σ) :=
    (□∀ arg, □close argT arg -∗ subtype' 0 0 (beta φ1 arg) (beta φ2 arg))%I.

  Definition lam_semEquiv {n} (argT : hoD 0 Σ) (φ1 φ2 : hoD (S n) Σ) :=
    (□∀ arg, □close argT arg -∗ semEquiv 0 0 (beta φ1 arg) (beta φ2 arg))%I.

  (* Here, we inherit eta from the metalanguage, in both directions. *)
  Lemma eta1 {n} argT (φ : hoD (S n) Σ): lam_subtype argT φ (λ v, φ v).
  Proof.
    rewrite /lam_subtype /subtype' /beta /=.
    iIntros "!>" (arg) "#Harg !>"; iIntros (args v Hcl) "? //".
  Qed.

  Lemma eta {n} argT (φ : hoD (S n) Σ): lam_semEquiv argT φ (λ v, φ v).
  Proof.
    rewrite /lam_semEquiv /semEquiv /beta /=.
    iIntros "!>" (arg) "#Harg !>"; iIntros (args v Hcl).
    by iApply wand_iff_refl.
  Qed.
End bar.

