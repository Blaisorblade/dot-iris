From iris.program_logic Require Export ectx_language ectxi_language.
From iris.algebra Require Export list ofe agree.
From iris.proofmode Require Export tactics.
From iris.base_logic Require Export lib.iprop (* For gname *)
     lib.saved_prop invariants.
From iris.program_logic Require Export weakestpre.

Require Export Dot.synFuncs.

Class dotG Σ := DotG {
  dotG_invG : invG Σ;
  dotG_savior :> savedAnythingG Σ (list vl -c> vl -c> ▶ ∙)
}.

Class dotPreG Σ := DotPreG {
  dotPreG_invG : invPreG Σ;
  dotPreG_savior :> savedAnythingG Σ (list vl -c> vl -c> ▶ ∙)
}.

Definition dotΣ := #[invΣ; savedAnythingΣ (list vl -c> vl -c> ▶ ∙)].

Instance subG_dotΣ {Σ} : subG dotΣ Σ → dotPreG Σ.
Proof. solve_inG. Qed.

(** saved interpretations *)

Section saved_interp.
  Context `{!dotG Σ}.

  Definition saved_interp_own (γ : gname) (Φ : list vl → vl → iProp Σ) :=
    saved_anything_own
      (F := list vl -c> vl -c> ▶ ∙) γ (λ vs v, CofeMor Next (Φ vs v)).

Instance saved_interp_own_contractive γ :
  Contractive (saved_interp_own γ : (list vl -c> vl -c> iProp Σ) → iProp Σ).
Proof.
  intros n X Y HXY.
  rewrite /saved_interp_own /saved_anything_own /=.
  f_equiv. apply to_agree_ne; f_equiv.
  intros x y.
  apply Next_contractive.
  destruct n; simpl in *; auto.
  apply HXY.
Qed.

Lemma saved_interp_alloc_strong (G : gset gname) (Φ : list vl → vl → iProp Σ) :
  (|==> ∃ γ, ⌜γ ∉ G⌝ ∧ saved_interp_own γ Φ)%I.
Proof. iApply saved_anything_alloc_strong. Qed.

Lemma saved_interp_alloc (Φ : list vl → vl → iProp Σ) :
  (|==> ∃ γ, saved_interp_own γ Φ)%I.
Proof. iApply saved_anything_alloc. Qed.

Lemma saved_interp_agree γ Φ Ψ vs v :
  saved_interp_own γ Φ -∗ saved_interp_own γ Ψ -∗ ▷ (Φ vs v ≡ Ψ vs v).
Proof.
  unfold saved_pred_own. iIntros "#HΦ #HΨ /=". iApply bi.later_equivI.
  iDestruct (saved_anything_agree with "HΦ HΨ") as "Heq".
  rewrite bi.ofe_fun_equivI; iSpecialize ("Heq" $! vs).
  by rewrite bi.ofe_fun_equivI; iSpecialize ("Heq" $! v); simpl.
Qed.

Lemma saved_interp_impl γ Φ Ψ vs v :
  saved_interp_own γ Φ -∗ saved_interp_own γ Ψ -∗ □ (▷ Φ vs v -∗ ▷ Ψ vs v).
Proof.
  unfold saved_pred_own. iIntros "#HΦ #HΨ /= !# H1".
  iDestruct (saved_anything_agree with "HΦ HΨ") as "Heq".
  rewrite bi.ofe_fun_equivI; iSpecialize ("Heq" $! vs).
  rewrite bi.ofe_fun_equivI; iSpecialize ("Heq" $! v); simpl.
  rewrite bi.later_equivI.
  by iNext; iRewrite -"Heq".
Qed.

End saved_interp.

(** Instantiating iris with  *)
Module lang.

Definition to_val (t: tm) : option vl :=
  match t with
  | tv v => Some v
  | _ => None
  end.

Definition of_val: vl -> tm := tv.

Inductive ectx_item :=
| AppLCtx (e2: tm)
| AppRCtx (v1: vl)
| ProjCtx (l: label).

Definition fill_item (Ki : ectx_item) (e : tm) : tm :=
  match Ki with
  | AppLCtx e2 => tapp e e2
  | AppRCtx v1 => tapp (tv v1) e
  | ProjCtx l => tproj e l
  end.

Definition state := unit.
Definition observation := unit.

Inductive head_step : tm -> state -> list observation -> tm -> state -> list tm -> Prop :=
| st_beta t1 v2 σ:
    head_step (tapp (tv (vabs t1)) (tv v2)) σ [] (t1.|[v2/]) σ []
| st_proj ds l σ v:
    reverse (selfSubst ds) !! l = Some (dvl v) ->
    head_step (tproj (tv (vobj ds)) l) σ [] (tv v) σ []
| st_skip t σ:
    head_step (tskip t) σ [] t σ [].

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. done. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert v; induction e; intros; simplify_option_eq; auto with f_equal.
Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

Lemma val_stuck e1 σ1 k e2 σ2 ef :
  head_step e1 σ1 k e2 σ2 ef → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 k e2 σ2 ef :
  head_step (fill_item Ki e) σ1 k e2 σ2 ef → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
    repeat match goal with
           | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
           end; auto.
Qed.

Lemma dot_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
split; apply _ || eauto using to_of_val, of_to_val, val_stuck,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
Qed.

End lang.

Canonical Structure dot_ectxi_lang := EctxiLanguage lang.dot_lang_mixin.
Canonical Structure dot_ectx_lang := EctxLanguageOfEctxi dot_ectxi_lang.
Canonical Structure dot_lang := LanguageOfEctx dot_ectx_lang.

Instance dotG_irisG `{dotG Σ} : irisG dot_lang Σ := {
  iris_invG := dotG_invG;
  state_interp σ κs _ := True%I;
  fork_post _ := True%I;
}.

Section Sec.
  Context `{dotG Σ}.

  Canonical Structure vlC := leibnizC vl.
  Canonical Structure tmC := leibnizC tm.
  Canonical Structure dmC := leibnizC dm.
  Canonical Structure dmsC := leibnizC dms.
  Canonical Structure pathC := leibnizC path.

  Canonical Structure listVlC := leibnizC (list vl).
End Sec.

Notation envD Σ := (listVlC -n> vlC -n> iProp Σ).
Notation "g ⤇ p" := (saved_interp_own g p) (at level 20).

(* Class dotUInterpG Σ := DotInterpG { *)
(*   dot_uinterp: ty -> envD Σ *)
(* }. *)
