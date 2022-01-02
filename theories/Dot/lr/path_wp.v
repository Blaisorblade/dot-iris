(** * gDOT's path weakest precondition [path_wp].
Constructing Iris least fixpoints is relatively involved; but lemma
[path_wp_unfold] witnesses that [path_wp] is the fixpoint of [path_wp_pre].
The defining equations are proven as lemmas [path_wp_pv_eq] and
[path_wp_pself_eq].
*)
From D Require Import iris_prelude iris_extra.det_reduction.
From D.Dot Require Import dlang_inst rules lr_syn_aux path_repl.
From D.pure_program_logic Require Import lifting.

Implicit Types
         (L T U : ty) (v : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (Γ : ctx) (ρ : env) (Pv : vl → Prop).

Set Suggest Proof Using.
Set Default Proof Using "Type".

(** A simplified variant of weakest preconditions for path evaluation.
The difference is that path evaluation is completely pure, and
postconditions must hold now, not after updating resources.
vp ("Value from Path") and vq range over results of evaluating paths.
Below, we define a version internal to Iris, following Iris's total weakest
precondition. *)

From iris.bi Require Import fixpoint big_op.
(* From iris.program_logic Require Export weakestpre. *)
Set Default Proof Using "Type".
Import uPred.

Canonical Structure pathO := leibnizO path.

Section path_wp_pre.
  Context {Σ : gFunctors}.
  Implicit Types (φ : vl -d> iPropO Σ).

  (** The definition of total weakest preconditions is very similar to the
  definition of normal (i.e. partial) weakest precondition, with the exception
  that there is no later modality. Hence, instead of taking a Banach's fixpoint,
  we take a least fixpoint. *)
  Definition path_wp_pre (path_wp : pathO → (vl -d> iPropO Σ) → iProp Σ) p φ : iProp Σ :=
    match p with
    | pv vp => φ vp
    | pself p l => ∃ vp q, ⌜ vp @ l ↘ dpt q ⌝ ∧
        path_wp p (λ v, ⌜ vp = v ⌝) ∧ path_wp q φ
    end.

  Lemma path_wp_pre_mono (wp1 wp2 : path → (vl -d> iPropO Σ) → iProp Σ) :
    ⊢ (∀ p Φ, wp1 p Φ -∗ wp2 p Φ) →
    ∀ p Φ, path_wp_pre wp1 p Φ -∗ path_wp_pre wp2 p Φ.
  Proof.
    iIntros "H"; iIntros (p1 Φ). rewrite /path_wp_pre /=.
    destruct (p1) as [v|]; first by iIntros.
    iDestruct 1 as (vp q Hlook) "Hpq".
    iExists vp, q. iFrame (Hlook).
    iSplit; iApply "H".
    iDestruct "Hpq" as "[$ _]".
    iDestruct "Hpq" as "[_ $]".
  Qed.

  (* Uncurry [path_wp_pre] and equip its type with an OFE structure *)
  Definition path_wp_pre' :
      (prodO pathO (vl -d> iPropO Σ) → iPropO Σ) →
      (prodO pathO (vl -d> iPropO Σ) → iPropO Σ) :=
    Datatypes.uncurry ∘ path_wp_pre ∘ Datatypes.curry.
End path_wp_pre.

#[local] Instance path_wp_pre_mono' {Σ} : BiMonoPred (@path_wp_pre' Σ).
Proof.
  constructor.
  - iIntros (wp1 wp2) "#H". iIntros ([p Φ]); iRevert (p Φ).
    iApply path_wp_pre_mono. iIntros (p Φ). iApply ("H" $! (p,Φ)).
  - intros wp Hwp n [p1 Φ1] [p2 Φ2] [?%leibniz_equiv Heq]; simplify_eq/=.
    rewrite /Datatypes.curry /path_wp_pre; solve_proper_ho.
Qed.

Definition path_wp_def `{!dlangG Σ} p φ : iProp Σ := bi_least_fixpoint path_wp_pre' (p, φ).
Definition path_wp_aux `{!dlangG Σ} : seal path_wp_def. Proof. by eexists. Qed.
Definition path_wp `{!dlangG Σ} := path_wp_aux.(unseal).
Definition path_wp_unseal `{!dlangG Σ} : path_wp = path_wp_def := path_wp_aux.(seal_eq).

#[global] Instance : Params (@path_wp) 2 := {}.

Section path_wp_lemmas.
  Context `{!dlangG Σ}.
  #[local] Notation path_wp := (path_wp (Σ := Σ)).

  Implicit Types (φ Φ : vl -d> iPropO Σ).

  Lemma path_wp_unfold p Φ : path_wp p Φ ⊣⊢ path_wp_pre path_wp p Φ.
  Proof. by rewrite path_wp_unseal /path_wp_def least_fixpoint_unfold. Qed.

  Lemma path_wp_pv_eq v φ : path_wp (pv v) φ ⊣⊢ φ v.
  Proof. by rewrite path_wp_unfold. Qed.
  Lemma path_wp_pself_eq p l φ :
    path_wp (pself p l) φ ⊣⊢
      ∃ vp q, ⌜ vp @ l ↘ dpt q ⌝ ∧ path_wp p (λ v, ⌜ vp = v ⌝) ∧ path_wp q φ.
  Proof. by rewrite path_wp_unfold. Qed.

  (* General induction principle on path_wp. *)
  Lemma path_wp_ind' Ψ
    (HΨ : ∀ n p, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ p)) :
    ⊢ (∀ p Φ, path_wp_pre (λ p Φ, Ψ p Φ ∧ path_wp p Φ) p Φ -∗ Ψ p Φ) →
    ∀ p Φ, path_wp p Φ -∗ Ψ p Φ.
  Proof.
    iIntros "#IH" (p Φ) "H". rewrite path_wp_unseal.
    set (Ψ' := uncurry Ψ : prodO pathO (vl -d> iPropO Σ) → iPropO Σ).
    have ? : NonExpansive Ψ'.
    { intros n [p1 Φ1] [p2 Φ2] [?%leibniz_equiv ?]; simplify_eq/=. by apply HΨ. }
    iApply (least_fixpoint_strong_ind _ Ψ' with "[] H").
    iIntros "!>" ([? ?]) "H". by iApply "IH".
  Qed.

  (* Specialized induction principle on path_wp. *)
  Lemma path_wp_ind Ψ
    (Hprop : ∀ n p, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ p)) :
    ⊢ (∀ v Φ, Φ v -∗ Ψ (pv v) Φ) →
     (∀ p l Φ, path_wp_pre (λ p Φ, Ψ p Φ ∧ path_wp p Φ) (pself p l) Φ -∗ Ψ (pself p l) Φ) →
     ∀ p Φ, path_wp p Φ -∗ Ψ p Φ.
  Proof.
    iIntros "#Hpv #Hpself" (p Φ) "Hp". iApply (path_wp_ind' with "[] Hp").
    iIntros ([|?p l]); iIntros; by [iApply "Hpv"| iApply "Hpself"].
  Qed.
  Ltac path_wp_ind p φ := iRevert (p φ);
    iApply path_wp_ind; first solve_proper;
      rewrite /path_wp_pre ?path_wp_unfold /=.

  #[global] Instance path_wp_ne p n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (path_wp p).
  Proof.
    intros Φ1 Φ2 HΦ. rewrite !path_wp_unseal. by apply least_fixpoint_ne, pair_ne, HΦ.
  Qed.
  #[global] Instance path_wp_ne' p : NonExpansive (path_wp p).
  Proof. solve_proper. Qed.

  #[global] Instance path_wp_proper p :
    Proper (pointwise_relation _ (≡) ==> (≡)) (path_wp p).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply path_wp_ne=>v; apply equiv_dist.
  Qed.

  #[global] Instance pwp_proper : Proper ((=) ==> pointwise_relation _ (≡) ==> (≡)) path_wp.
  Proof.
    (* The induction works best in this shape, but this instance is best kept local. *)
    have pwp_proper_2 : ∀ p, Proper (pointwise_relation _ (≡) ==> (≡)) (path_wp p).
    by apply _.
    solve_proper.
  Qed.

  #[local] Hint Constructors path_wp_pure : core.

  Lemma path_wp_pureable p Pv :
    path_wp p (λ v, ⌜Pv v⌝) ⊣⊢ ⌜path_wp_pure p Pv⌝.
  Proof.
    iSplit.
    - move HE: (λI v : vl, ⌜Pv v⌝) => φ.
      (* Internalize HE to ensure properness. *)
      iAssert ((φ : vl -d> iPropO Σ) ≡ (λ v : vl, ⌜Pv v⌝))%I as "HE".
      by simplify_eq.
      clear HE; iIntros "H"; iRevert (Pv) "HE"; iRevert "H"; path_wp_ind p φ.
      + iIntros "* Hv" (Pv) "Heq"; rewrite discrete_fun_equivI /=.
        iRewrite ("Heq" $! v) in "Hv". iDestruct "Hv" as %Hv. auto.
      + iDestruct 1 as (vp q Hlook) "[[IHp _] [IHq _]]"; iIntros (Pv) "Heq".
        iDestruct ("IHq" with "Heq") as %Hq.
        iDestruct ("IHp" $! (eq vp) with "[//]") as %Hp. eauto.
    - iIntros (Hp); iInduction Hp as [] "IH"; iEval (rewrite path_wp_unfold /=); eauto.
  Qed.

  Lemma path_wp_eq p φ :
    path_wp p φ ⊣⊢ ∃ v, ⌜ path_wp_pure p (eq v) ⌝ ∧ φ v.
  Proof.
    iSplit.
    - path_wp_ind p φ; first by eauto 10.
      iDestruct 1 as (vp q Hlook) "[[IHp _] [IHq _]]".
      iDestruct ("IHp") as %(? & Hp & <-).
      iDestruct ("IHq") as (vq Hq) "H".
      iExists vq; eauto.
    - iDestruct 1 as (v Hwp) "H".
      move: Hwp; move HE: (eq v) => φ' Hwp.
      iInduction Hwp as [|] "IH"; simplify_eq/=;
        iEval (rewrite path_wp_unfold /=); first done.
      iExists _, _. by repeat iSplit; [|iApply path_wp_pureable|iApply "IH1"].
  Qed.

  Lemma strong_path_wp_wand i φ1 φ2 p :
    ▷^i path_wp p φ1 -∗
    (∀ v, ⌜ path_wp_pure p (eq v) ⌝ -∗ ▷^i φ1 v -∗ ▷^i φ2 v) -∗
    ▷^i path_wp p φ2.
  Proof.
    rewrite !path_wp_eq. iIntros "Hi Hwand"; iDestruct "Hi" as (v) "[#Hal H1]".
    iExists v; iFrame "Hal".
    iApply (strip_pure_laterN_impl with "[-] Hal"); iIntros (Hal).
    iApply ("Hwand" $! v Hal with "H1").
  Qed.

  Lemma path_wp_wand_laterN i φ1 φ2 p :
    ▷^i path_wp p φ1 -∗ (∀ v, ▷^i φ1 v -∗ ▷^i φ2 v) -∗ ▷^i path_wp p φ2.
  Proof.
    iIntros "H1 Hwand". iApply (strong_path_wp_wand with "H1").
    iIntros "* _"; iApply "Hwand".
  Qed.

  Lemma path_wp_wand φ1 φ2 p :
    path_wp p φ1 -∗ (∀ v, φ1 v -∗ φ2 v) -∗ path_wp p φ2.
  Proof. apply (path_wp_wand_laterN 0). Qed.

  #[global] Instance path_wp_pureableI p φ Pv :
    (∀ v, IntoPure (φ v) (Pv v)) →
    IntoPure (path_wp p φ) (path_wp_pure p Pv).
  Proof.
    rewrite /IntoPure -path_wp_pureable; iIntros (Hw) "Hp".
    iApply (path_wp_wand with "Hp"). iIntros (v). iApply Hw.
  Qed.
  #[global] Instance path_wp_pureableF p φ Pv b :
    (∀ v, FromPure b (φ v) (Pv v)) →
    FromPure false (path_wp p φ) (path_wp_pure p Pv).
  Proof.
    rewrite /FromPure/= -path_wp_pureable. iIntros (Hw) "Hp".
    iApply (path_wp_wand with "Hp"); iIntros (v Hpv); iApply Hw.
    by case: b {Hw} => /=; iFrame (Hpv).
  Qed.

  Lemma path_wp_det p v1 v2 :
    path_wp p (λ w, ⌜ v1 = w ⌝) -∗
    path_wp p (λ w, ⌜ v2 = w ⌝) -∗
    ⌜ v1 = v2 ⌝ : iProp Σ.
  Proof. iIntros "!%". exact: path_wp_pure_det. Qed.

  Lemma path_wp_swap p u :
    path_wp p (λ w, ⌜w = u⌝) ⊣⊢ path_wp p (λ w, ⌜u = w⌝).
  Proof. iIntros "!%". by rewrite /= path_wp_pure_swap. Qed.

  (* Not provable through pure props for impure [φ]. *)
  Lemma alias_paths_samepwp p q :
    alias_paths p q ↔
      (∃ u, path_wp_pure p (eq u)) ∧
      ∀ φ, path_wp p φ ≡ path_wp q φ.
  Proof.
    split.
    - move => Hal; have /alias_paths_sameres [v [Hp Hq]] := Hal.
      split; first by [eauto]; intros φ; rewrite !path_wp_eq.
      f_equiv => w. do 2 f_equiv. apply alias_paths_elim_eq_pure, Hal.
    - rewrite alias_paths_sameres. destruct 1 as ((u & Hp) & Heq).
      exists u; split; first done.
      (* Yes, very weird. *)
      apply (pure_soundness (M := iResUR Σ)).
      iRevert (Hp). by rewrite -!path_wp_pureable Heq.
  Qed.

  Lemma alias_paths_elim_eq φ {p q} :
    alias_paths p q →
    path_wp p φ ≡ path_wp q φ.
  Proof. intros ?%alias_paths_samepwp. intuition. Qed.

  Lemma path_wp_and p Φ1 Φ2 :
    path_wp p Φ1 ∧ path_wp p Φ2 ⊣⊢
    path_wp p (λ v, Φ1 v ∧ Φ2 v).
  Proof.
    rewrite !path_wp_eq and_exist_r; f_equiv => v.
    rewrite !(assoc bi_and) ![(⌜_⌝ ∧ _)%I](comm bi_and) -!(assoc bi_and).
    f_equiv; apply /and_pure_equiv => Hv1.
    iSplit; last by eauto.
    iDestruct 1 as (v2 Hv2) "H2". by rewrite -(path_wp_pure_det Hv1 Hv2).
  Qed.

  Lemma path_wp_and' p Φ1 Φ2 :
    path_wp p Φ1 -∗ path_wp p Φ2 -∗
    path_wp p (λ v, Φ1 v ∧ Φ2 v).
  Proof. rewrite -path_wp_and; iIntros "$ $". Qed.

  Lemma path_wp_agree p Φ1 Φ2 :
    path_wp p Φ1 -∗ path_wp p Φ2 -∗
    ∃ v, ⌜ path_wp_pure p (eq v) ⌝ ∧ Φ1 v ∧ Φ2 v.
  Proof. rewrite -path_wp_eq. exact: path_wp_and'. Qed.

  Lemma path_wp_or p Φ1 Φ2 :
    path_wp p Φ1 ∨ path_wp p Φ2 ⊣⊢
    path_wp p (λ v, Φ1 v ∨ Φ2 v).
  Proof.
    rewrite !path_wp_eq; iSplit.
    - iIntros "[H|H]"; iDestruct "H" as (v Hv) "H"; eauto.
    - iDestruct 1 as (v Hv) "[H|H]"; eauto.
  Qed.

  Lemma path_wp_later_swap p φ :
    path_wp p (λ v, ▷ φ v) ⊢ ▷ path_wp p (λ v, φ v).
  Proof. rewrite !path_wp_eq. by iDestruct 1 as (v Hp) "H"; eauto. Qed.

  Lemma path_wp_laterN_swap p φ i :
    path_wp p (λ v, ▷^i φ v) ⊢ ▷^i path_wp p (λ v, φ v).
  Proof. elim: i => [//|i /= <-]. apply path_wp_later_swap. Qed.

  Lemma path_wp_exec p v :
    path_wp p (λ w, ⌜ v = w ⌝) ⊢@{iPropI Σ}
    ⌜ ∃ n, PureExec True n (path2tm p) (tv v) ⌝.
  Proof. iIntros "!%". apply path_wp_exec_pure. Qed.

  Lemma path_wp_pure_exec p φ :
    path_wp p φ ⊢ ∃ v, ⌜ ∃ n, PureExec True n (path2tm p) (tv v) ⌝ ∧ φ v.
  Proof.
    rewrite path_wp_eq. setoid_rewrite <-path_wp_exec.
    iDestruct 1 as (v Hcl) "H". eauto.
  Qed.

  Lemma path_wp_to_wp p φ :
    path_wp p (λ v, φ v) -∗
    WP (path2tm p) {{ v, φ v }}.
  Proof.
    rewrite path_wp_pure_exec; iDestruct 1 as (v [n Hex]) "H".
    by wp_pure.
  Qed.

  Lemma path_wp_pure_to_wp {p v} (Hpwpp : path_wp_pure p (eq v)) :
    ⊢ WP (path2tm p) {{ w, ⌜ v = w ⌝ }}.
  Proof. rewrite -path_wp_to_wp. by iIntros "!%". Qed.

  #[global] Instance path_wp_timeless p Pv : Timeless (path_wp p (λI v, ⌜Pv v⌝)).
  Proof. rewrite path_wp_pureable. apply _. Qed.

  Lemma path_wp_terminates p φ :
    path_wp p φ ⊢ ⌜ terminates (path2tm p) ⌝.
  Proof.
    rewrite path_wp_pure_exec; iDestruct 1 as (v [n Hp]) "_"; iIntros "!%".
    exact: PureExec_to_terminates.
  Qed.
End path_wp_lemmas.
