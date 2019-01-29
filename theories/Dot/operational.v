From iris.program_logic Require Import ectx_language ectxi_language.
From iris.algebra Require Import ofe agree.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.iprop (* For gname *)
     lib.saved_prop invariants.
From iris.program_logic Require Import weakestpre.

From D Require Import tactics.
From D.Dot Require Export dotsyn.

Class dotG Σ := DotG {
  dotG_invG : invG Σ;
  dotG_savior :> savedAnythingG Σ (vls -c> vl -c> ▶ ∙)
}.

Class dotPreG Σ := DotPreG {
  dotPreG_invG : invPreG Σ;
  dotPreG_savior :> savedAnythingG Σ (vls -c> vl -c> ▶ ∙)
}.

Definition dotΣ := #[invΣ; savedAnythingΣ (vls -c> vl -c> ▶ ∙)].

Instance subG_dotΣ {Σ} : subG dotΣ Σ → dotPreG Σ.
Proof. solve_inG. Qed.

(** saved interpretations *)

Section saved_interp.
  Context `{!dotG Σ}.

  Definition saved_interp_own (γ : gname) (Φ : vls → vl → iProp Σ) :=
    saved_anything_own
      (F := vls -c> vl -c> ▶ ∙) γ (λ vs v, CofeMor Next (Φ vs v)).

Instance saved_interp_own_contractive γ :
  Contractive (saved_interp_own γ : (vls -c> vl -c> iProp Σ) → iProp Σ).
Proof.
  intros n X Y HXY.
  rewrite /saved_interp_own /saved_anything_own /=.
  f_equiv. apply to_agree_ne; f_equiv.
  intros x y.
  apply Next_contractive.
  destruct n; simpl in *; auto.
  apply HXY.
Qed.

Lemma saved_interp_alloc_strong (G : gset gname) (Φ : vls → vl → iProp Σ) :
  (|==> ∃ γ, ⌜γ ∉ G⌝ ∧ saved_interp_own γ Φ)%I.
Proof. iApply saved_anything_alloc_strong. Qed.

Lemma saved_interp_alloc (Φ : vls → vl → iProp Σ) :
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

Lemma saved_interp_agree_eta γ Φ Ψ vs v :
  saved_interp_own γ (λ (vs : vls) (v : vl), (Φ vs) v) -∗
  saved_interp_own γ (λ (vs : vls) (v : vl), (Ψ vs) v) -∗
  ▷ (Φ vs v ≡ Ψ vs v).
Proof.
  iIntros "#H1 #H2".  
  repeat change (fun x => ?h x) with h.
  by iApply saved_interp_agree.
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

Implicit Types
         (T: ty) (v: vl) (t e: tm) (d: dm) (ds: dms) (vs: vls)
         (Γ : ctx).
(** Substitute object inside itself (to give semantics to the "self"
    variable). To use when descending under the [vobj] binder. *)
Definition selfSubst ds: dms := ds.|[vobj ds/].

(* Unset Program Cases. *)
(* Definition gmap_of_dms ds: gmap label dm := map_of_list ds. *)
(* Definition dms_lookup l ds := gmap_of_dms ds !! l. *)
(* Arguments gmap_of_dms /. *)
(* Arguments dms_lookup /. *)

Definition objLookup v (l: label) d: Prop :=
  ∃ ds, v = vobj ds ∧ (dms_lookup l (selfSubst ds)) = Some d.
Notation "v @ l ↘ d" := (objLookup v l d) (at level 20).

(** Instead of letting obj_opens_to autounfold,
    provide tactics to show it's deterministic and so on. *)

(** Rewrite v ↗ ds to vobj ds' ↗ ds. *)
Ltac simplOpen ds :=
  lazymatch goal with
  | H: ?v @ ?l ↘ ?d |-_=>
    inversion H as (ds & -> & _)
  end.

(** Determinacy of obj_opens_to. *)
Lemma objLookupDet v l d1 d2: v @ l ↘ d1 -> v @ l ↘ d2 -> d1 = d2.
Proof.
  rewrite /objLookup; intros; ev; by subst; injectHyps; optFuncs_det.
Qed.
Ltac objLookupDet :=
  lazymatch goal with
  | H1: ?v @ ?l ↘ ?d1, H2: ?v @ ?l ↘ ?d2 |- _=>
    assert (d2 = d1) as ? by (eapply objLookupDet; eassumption); injectHyps
  end.

(* Section AboutObjLookup. *)
(** Auxiliary definitions to prove [lookup_reverse_length], since a direct inductive proof appers to fail (but
see rev_append_map for an approach that has a chance). *)
(* Fixpoint indexr {X} (i: nat) (xs: list X) : option X := *)
(*   match xs with *)
(*   | [] => None *)
(*   | x :: xs => *)
(*     if decide (i = length xs) then Some x else indexr i xs *)
(*   end. *)

(* Lemma indexr_max {X} (x: X) i xs: *)
(*                        indexr i xs = Some x -> *)
(*                        i < length xs. *)
(* Proof. *)
(*   induction xs; first done; rewrite /lt in IHxs |- *; move => /= H. *)
(*   case_decide; subst; [ lia | eauto ]. *)
(* Qed. *)
(* Hint Resolve indexr_max. *)

(* Lemma lookup_reverse_indexr {X} (ds: list X) l: reverse ds !! l = indexr l ds. *)
(* Proof. *)
(*   elim: ds l => [|d ds IHds] l //=. *)
(*   case_decide; subst. *)
(*   - by rewrite reverse_cons lookup_app_r reverse_length ?Nat.sub_diag. *)
(*   - case (decide (l < length ds)) => Hl. *)
(*     + by rewrite reverse_cons lookup_app_l ?reverse_length. *)
(*     + assert (l > length ds) by omega. *)
(*       assert (indexr l ds = None). { *)
(*         destruct (indexr l ds) eqn:? => //. *)
(*         assert (l < length ds) by (eapply indexr_max; eauto). *)
(*         lia. *)
(*       } *)
(*       by rewrite lookup_ge_None_2 ?reverse_length. *)
(* Qed. *)

(* Lemma lookup_reverse_length {X} l (x: X) xs: l = length xs → reverse (x :: xs) !! l = Some x. *)
(* Proof. *)
(*   intros; subst. rewrite lookup_reverse_indexr /=. case_decide => //=. *)
(* Qed. *)

(* Lemma obj_lookup_cons d ds l: (l, d) ∈ ds → vobj ds @ l ↘ d.|[vobj ds/]. *)
(* Proof. *)
(*   hnf; move => Hin; eexists; split => //=. *)
(*   elim: ds Hin => [|[l' d'] ds IHds] //= Hin; first inversion Hin. *)
(*   (* destruct (decide (l = l')) as [-> | Hne]. *) *)
(*   inverse Hin; rewrite ?lookup_insert /mapsnd //=. *)
(*   apply IHds in H1. *)
(*   destruct (decide (l = l')) as [Heq | Hne]. *)
(*   admit. *)
(*   cbn. *)
(*   asimpl. cbn. *)
(*   f_equal. *)
(*   rewrite /selfSubst /=. *)
  
(*   assert ((l, d.|[vobj ds/]) ∈ ds.|[vobj ds/]). *)
(*   rewrite /hsubst /list_pair_hsubst -/mapsnd. *)
(*   set (sb := (hsubst (vobj ds .: ids))). *)
(*   assert (map (mapsnd ) (l, d.|[vobj ds/]) ∈ ds.|[vobj ds/]). *)
  
(*   Search "_ ∈ _". *)
(*   assert ((l, d) ∈ gmap_of_dms ds). *)
(*   apply lookup_reverse_length. by rewrite map_length. *)
(* Qed. *)

(* Lemma indexr_extend {X} vs n x (T: X): *)
(*                        indexr n vs = Some T -> *)
(*                        indexr n (x::vs) = Some T. *)
(* Proof. *)
(*   move => H /=; assert (n < length vs) by naive_solver; by case_decide; first lia. *)
(* Qed. *)
(* Hint Resolve indexr_extend. *)

(* Lemma lookup_reverse_extend {X} l (d: X) ds: *)
(*   reverse ds !! l = Some d → *)
(*   reverse (d :: ds) !! l = Some d. *)
(* Proof. *)
(*   intros; subst. rewrite -> lookup_reverse_indexr in *. by apply indexr_extend. *)
(* Qed. *)

(* Lemma rev_append_map {X Y} (xs1 xs2: list X) (f: X → Y): rev_append (map f xs1) (map f xs2) = map f (rev_append xs1 xs2). *)
(* Proof. *)
(*   elim: xs1 xs2 => [|x xs1 IH] xs2 //=. eapply (IH (x :: xs2)). *)
(* Qed. *)
(* Lemma reverse_map {X Y} (xs: list X) (f: X → Y): reverse (map f xs) = map f (reverse xs). *)
(* Proof. rewrite /reverse. eapply (rev_append_map xs []). Qed. *)

(* Lemma lookup_map {X Y} x (xs: list X) (f: X → Y) l: xs !! l = Some x → map f xs !! l = Some (f x). *)
(* Proof. *)
(*   elim: xs l => /= [|x' xs IH] [|l] //= Hl; by [cinject Hl | apply IH]. *)
(* Qed. *)

(* (* Lemma lookup_map_inv {X Y} x (xs: list X) (f: X → Y) l: map f xs !! l = Some (f x) → xs !! l = Some x. *) *)
(* (* Proof. *) *)
(* (*   elim: xs l => [|x' xs IH] [|l] //=. (* ONLY FOR F INDUCTIVE! *) *) *)

(* (* Lemma obj_lookup_extend d ds l: *) *)
(* (*   vobj ds @ l ↘ d.|[vobj ds/] → *) *)
(* (*   vobj (d :: ds) @ l ↘ d.|[vobj (d :: ds)/]. *) *)
(* (* Proof. *) *)
(* (*   hnf. *) *)
(* (*   intros (ds0 & Heq & Hl). cinject Heq. *) *)
(* (*   eexists; split; trivial. *) *)
(* (*   move: Hl. rewrite /selfSubst /lookup_reverse_indexr /= => Hl. *) *)
(* (*   apply lookup_reverse_extend. *) *)
(* (*   move: Hl. rewrite /hsubst /HSubst_dm !reverse_map => Hl. *) *)
(* (*   apply lookup_map. apply lookup_map_inv in Hl. apply Hl. *) *)
(* (*   (* eauto using lookup_map, lookup_map_inv. *) *) *)
(* (* Qed. *) *)

(* End AboutObjLookup. *)

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
    dms_lookup l (selfSubst ds) = Some (dvl v) ->
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

Export lang.

Section Sec.
  Context `{dotG Σ}.

  Canonical Structure vlC := leibnizC vl.
  Canonical Structure tmC := leibnizC tm.
  Canonical Structure dmC := leibnizC dm.
  Canonical Structure dmsC := leibnizC dms.
  Canonical Structure pathC := leibnizC path.

  Canonical Structure listVlC := leibnizC (list vl).
End Sec.

Notation "g ⤇ p" := (saved_interp_own g p) (at level 20).

(* For abstracting synToSem. *)
Class dotInterpG Σ := DotInterpG {
  dot_interp: ty -> vls -> vl -> iProp Σ
}.
