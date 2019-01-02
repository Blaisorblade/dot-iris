From iris.program_logic Require Import ectx_language ectxi_language.
From iris.algebra Require Import ofe agree.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.iprop (* For gname *)
     lib.saved_prop invariants.
From iris.program_logic Require Import weakestpre.

From Dot Require Import tactics.
From DSub Require Export syn.

(** Instantiating iris with DSub *)
Module lang.

Definition to_val (t: tm) : option vl :=
  match t with
  | tv v => Some v
  | _ => None
  end.

Definition of_val: vl -> tm := tv.

Inductive ectx_item :=
| AppLCtx (e2: tm)
| AppRCtx (v1: vl).

Definition fill_item (Ki : ectx_item) (e : tm) : tm :=
  match Ki with
  | AppLCtx e2 => tapp e e2
  | AppRCtx v1 => tapp (tv v1) e
  end.

Definition state := unit.
Definition observation := unit.

Inductive head_step : tm -> state -> list observation -> tm -> state -> list tm -> Prop :=
| st_beta t1 v2 σ:
    head_step (tapp (tv (vabs t1)) (tv v2)) σ [] (t1.|[v2/]) σ []
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

Lemma dsub_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
split; apply _ || eauto using to_of_val, of_to_val, val_stuck,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
Qed.

End lang.

Export lang.

Canonical Structure dsub_ectxi_lang := EctxiLanguage lang.dsub_lang_mixin.
Canonical Structure dsub_ectx_lang := EctxLanguageOfEctxi dsub_ectxi_lang.
Canonical Structure dsub_lang := LanguageOfEctx dsub_ectx_lang.

Canonical Structure vlC := leibnizC vl.
Canonical Structure tmC := leibnizC tm.
Canonical Structure tyC := leibnizC ty.

Canonical Structure listVlC := leibnizC (list vl).

From stdpp Require Import gmap.
From iris.algebra Require Import gmap.
From iris.base_logic.lib Require Import gen_heap.

Class dsubG Σ := DsubG {
  dsubG_invG : invG Σ;
  dsubG_savior :> savedAnythingG Σ (vls -c> vl -c> ▶ ∙);
  dsubG_types : gen_heapG stamp ty Σ;
  dsubG_interpNames : gen_heapG stamp gname Σ;
}.

Instance dsubG_irisG `{dsubG Σ} : irisG dsub_lang Σ := {
  iris_invG := dsubG_invG;
  state_interp σ κs _ := True%I;
  fork_post _ := True%I;
}.

Class dsubPreG Σ := DsubPreG {
  dsubPreG_invG : invPreG Σ;
  dsubPreG_savior :> savedAnythingG Σ (vls -c> vl -c> ▶ ∙);
  dsubPreG_types : gen_heapPreG stamp ty Σ;
  dsubPreG_interpNames : gen_heapPreG stamp gname Σ;
}.

Definition dsubΣ := #[invΣ; savedAnythingΣ (vls -c> vl -c> ▶ ∙); gen_heapΣ stamp ty; gen_heapΣ stamp gname].

Instance subG_dsubΣ {Σ} : subG dsubΣ Σ → dsubPreG Σ.
Proof. solve_inG. Qed.

(* For abstracting synToSem. *)
Class dsubInterpG Σ := DsubInterpG {
  dsub_interp: ty -> vls -> vl -> iProp Σ
}.

(** saved interpretations *)

Section saved_interp.
  Context `{!dsubG Σ}.

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

Notation "g ⤇ p" := (saved_interp_own g p) (at level 20).

Implicit Types
         (L T U: ty) (v: vl) (e: tm)
         (Γ : ctx).

Section translation.
  Definition stys := gmap stamp ty.
  Implicit Type g: stys.
  Fixpoint unstamp_tm g (t: tm): tm :=
    let fix go (t: tm): tm :=
        match t with
        | tv v => tv (unstamp_vl g v)
        | tapp t1 t2 => tapp (go t1) (go t2)
        | tskip t => tskip (go t)
        end
    in go t
  with
  unstamp_vl g (v: vl): vl :=
    let fix go (v: vl): vl :=
        match v with
        | vstamp vs s => vty (default TNat (g !! s)).|[to_subst vs]
        | vabs t => vabs (unstamp_tm g t)
        | vty T => vty (unstamp_ty g T)
        | vnat _ => v
        | var_vl _ => v
        end
    in go v
  with
  unstamp_ty g (T: ty): ty :=
    let fix go (T: ty): ty :=
        match T with
        | TTop => T
        | TBot => T
        | TAnd T1 T2 => TAnd (go T1) (go T2)
        | TOr T1 T2 => TOr (go T1) (go T2)
        | TLater T => TLater (go T)
        | TAll T1 T2 => TAll (go T1) (go T2)
        | TMu T => TMu (go T)
        | TTMem T1 T2 => TTMem (go T1) (go T2)
        | TSel v => TSel (unstamp_vl g v)
        | TSelA v T1 T2 => TSelA (unstamp_vl g v) (go T1) (go T2)
        | TNat => T
        end
    in go T.

  (* Not enough *)
  Definition stamps_tm e1 g e2 := e1 = unstamp_tm g e2.
  Definition stamps_vl v1 g v2 := v1 = unstamp_vl g v2.
  Definition stamps_ty T1 g T2 := T1 = unstamp_ty g T2.

  Definition emptystys: stys := ∅.
  Set Default Proof Using "Type".
  Lemma exists_stamped_vty_bad T: ∃ v' g, stamps_vl (vty T) g v'.
  Proof.
    assert (∃ s, s ∉ dom (gset stamp) emptystys) as [s H].
    exists (fresh (dom (gset stamp)emptystys)). by eapply not_elem_of_dom.

    (* exists (vstamp (idsσ 2) s). *)
    (* rewrite /stamps_vl /unstamp_vl /=. *)
    (* unfold push_var. *)
    (* rewrite ?to_subst_cons ?to_subst_nil. *)
    (* asimpl. *)

    (* exists (insert s T ∅); rewrite lookup_insert //=. *)
    exists (vstamp (idsσ 0) s); rewrite /stamps_vl /unstamp_vl /=; asimpl.
    exists (insert s T ∅); rewrite lookup_insert //=.
  Qed.
    (* unfold push_var. *)
    (* Check (@ids vl _). *)
    (* change (var_vl 0) with ((var_vl 0).[ren (+0)]). *)

    (* change (var_vl 0) with (@ids vl _ 0). *)
    (* replace (@ids vl _ 0 .: @ids vl _) with (@ids vl _). *)
    (* by asimpl. *)
    (* f_ext. move => [|x] //= . *)
  Lemma closed_subst_idsρ `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A) n :
    nclosed a n → a.|[to_subst (idsσ n)] = a.
  Admitted.

  Lemma exists_stamped_vty T n: nclosed T n → ∃ v' g, stamps_vl (vty T) g v'.
  Proof.
    assert (∃ s, s ∉ dom (gset stamp) emptystys) as [s H]. {
      exists (fresh (dom (gset stamp)emptystys)). by eapply not_elem_of_dom.
    }
    exists (vstamp (idsσ n) s); rewrite /stamps_vl /unstamp_vl /=; asimpl.
    exists (insert s T ∅); rewrite lookup_insert //=. by rewrite closed_subst_idsρ.
  Qed.

  Lemma closed_subst_id `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A) σ: nclosed a 0 → a.|[σ] = a.
  Proof.
    intro Hcl. rewrite (Hcl σ ids) /=; first by asimpl.
    intros; omega.
  Qed.

  Lemma subst_sigma_idsσ ρ n : length ρ = n →
                               (subst_sigma (idsσ n) ρ) = ρ.
  Proof.
    rewrite /subst_sigma. move :n.
    induction ρ => *; subst => //; asimpl.
    f_equal. by apply IHρ.
  Qed.

  Lemma foo f n x: x < n → to_subst (map f (idsσ n)) x = f (to_subst (idsσ n) x).
  Proof.
    induction n => //=; intros Hle. omega.
    destruct x => //=.
    asimpl.
    assert (x < n) as Hle' by omega. clear Hle.
    destruct (decide (S x < n)).
    (* asimpl; intros. omega. *)
    (* asimpl. hsubst_vls. *)
    (* inversion Hle. *)
    (* destruct (decide (x = 0)); subst => //=. *)
    (* destruct (decide (x = n)); subst; asimpl. *)
    (* admit. *)
    (* rewrite -IHn. *)
    (* subst => //; asimpl. *)
    (* rewrite /push_var; asimpl. *)
    (* intros x Hn. *)
    (* rewrite closed_subst_id. *)
  Abort.

  (* Same statement, try to prove it now. *)
  Lemma closed_subst_idsρ_try `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A) n :
    nclosed a n → a.|[to_subst (idsσ n)] = a.
  Proof.
    intro Hcl. rewrite (Hcl _ ids) /=; first by asimpl.
    clear a Hcl.
    Arguments push_var /.

    (* intros x Hle; induction x. *)
    (* destruct n => //. *)
    (* destruct n => //. *)
    (* asimpl. *)
    (* asimpl in IHx. *)
    (*   rewrite /push_var to_subst_cons. *)
    (*   simpl. *)
    (*   => /=. reflexivity. reflexivity. =>//. *)
    (* induction 0. *)

    induction n => //.
    intros x Hle.
    asimpl.
    destruct x => //=.
    assert (x < n) as Hle' by omega. clear Hle.
    transitivity ((to_subst (idsσ n) x).[ren (+1)]).

    unfold hsubst.
    generalize (subst (ren (+1))) as f => f.
    Abort.

  Lemma
    exists_stamped_vl t: ∃ t' g, stamps_vl t g t'
    with
    exists_stamped_tm t: ∃ t' g, stamps_tm t g t'
    with
    exists_stamped_ty t: ∃ t' g, stamps_ty t g t'.
  Proof.
    all: destruct t eqn:?; rewrite ?/stamps_tm ?/stamps_vl ?/stamps_ty; cbn.
    all: try by (exists t; exists ∅; subst; cbn).
    all: try lazymatch goal with
      | H : context [vstamp _] |- _ => fail
      | H : ?t = ?c ?t1 ?t2 |- _ =>
        (pose proof (exists_stamped_tm t1) as (t1' & g1 & Hre1) ||
        pose proof (exists_stamped_vl t1) as (t1' & g1 & Hre1) ||
        pose proof (exists_stamped_ty t1) as (t1' & g1 & Hre1));
        (pose proof (exists_stamped_tm t2) as (t2' & g2 & Hre2) ||
        pose proof (exists_stamped_vl t2) as (t2' & g2 & Hre2) ||
        pose proof (exists_stamped_ty t2) as (t2' & g2 & Hre2));
        assert (g2 = g1) as -> by admit; (* XXX False! *)
          rewrite Hre1 Hre2;
            exists (c t1' t2'); exists g1=>/=; by [f_equiv | destruct t1'; destruct t2']
      | H : ?t = ?c ?t1 |- _ =>
        pose proof (exists_stamped_tm t1) as (t1' & g1 & Hre) ||
        pose proof (exists_stamped_vl t1) as (t1' & g1 & Hre) ||
        pose proof (exists_stamped_ty t1) as (t1' & g1 & Hre);
          rewrite Hre;
            exists (c t1'); exists g1=>/=; by [f_equiv | destruct t1']
      end.
    admit.
        (pose proof (exists_stamped_tm t0_1) as (t1' & g1 & Hre1) ||
        pose proof (exists_stamped_vl t0_1) as (t1' & g1 & Hre1) ||
        pose proof (exists_stamped_ty t0_1) as (t1' & g1 & Hre1));
        (pose proof (exists_stamped_tm t0_2) as (t2' & g2 & Hre2) ||
        pose proof (exists_stamped_vl t0_2) as (t2' & g2 & Hre2) ||
        pose proof (exists_stamped_ty t0_2) as (t2' & g2 & Hre2));
    (* pose proof (exists_stamped_tm t0_1) as (t1' & g1 & Hre1); *)
      (* pose proof (exists_stamped_tm t0_2) as (t2' & g2 & Hre2); *)
    pose proof (exists_stamped_vl v) as (v' & g3 & Hre3);
    assert (g3 = g1) as -> by admit;
    assert (g2 = g1) as -> by admit; (* False. *)
          rewrite Hre1 Hre2 Hre3.

            exists (TSelA v' t1' t2'); exists g1=>/=;
          by [f_equiv; destruct t1'; destruct t2'].
  Admitted.

  Fixpoint t_tm n (t1 t2: tm) {struct t1}: Prop :=
    match (t1, t2) with
    | (tv v1, tv v2) => t_vl n v1 v2
    | (tapp t11 t12, tapp t21 t22) =>
      t_tm n t11 t21 ∧ t_tm n t12 t22
    | (tskip t1, tskip t2) =>
      t_tm n t1 t2
    | _ => False
    end
  with
  t_vl (n: nat) (v1 v2: vl) {struct v1}: Prop :=
    match (v1, v2) with
    | (var_vl i1, var_vl i2) => i1 = i2
    | (vabs t1, vabs t2) => t_tm (S n) t1 t2
    | (vnat n1, vnat n2) => n1 = n2
    | (vty T1, vstamp vs s) => 
    | _ => False
    end with
  t_ty n (T1 T2: ty) {struct T1}: Prop :=
    match (T1, T2) with
    | (TTop, TTop) => True
    | (TBot, TBot) => True
    | (TAnd T11 T12, TAnd T21 T22) =>
      t_ty n T11 T21 ∧ t_ty n T12 T22
    | (TOr T11 T12, TOr T21 T22) =>
      t_ty n T11 T21 ∧ t_ty n T12 T22
    | (TLater T1, TLater T2) =>
      t_ty n T1 T2
    | (TAll T11 T12, TAll T21 T22) =>
      t_ty n T11 T21 ∧ t_ty (S n) T12 T22
    | (TMu T1, TMu T2) =>
      t_ty (S n) T1 T2
    | (TTMem T11 T12, TTMem T21 T22) => t_ty n T11 T21 ∧ t_ty n T12 T22
    | (TSel v1, TSel v2) => t_vl n v1 v2
    | (TSelA v1 T11 T12, TSelA v2 T21 T22) => t_vl n v1 v2 ∧ t_ty n T11 T21 ∧ t_ty n T12 T22
    | (TNat, TNat) => True
    | _ => False
    end.

  with
  t_dm (d1 d2: dm) {struct d1}: iProp Σ :=
    match (d1, d2) with
    | (dtysyn T1, dtysem σ2 γ2) =>
      (* Only nontrivial case *)
      t_dty_syn2sem t_ty T1 σ2 γ2
    | (dvl v1, dvl v2) => t_vl v1 v2
    | _ => False
    end%I
  with
  t_path (p1 p2: path) {struct p1}: iProp Σ :=
    match (p1, p2) with
    | (pv v1, pv v2) => t_vl v1 v2
    | (pself p1 l1, pself p2 l2) => t_path p1 p2 ∧ ⌜l1 = l2⌝
    | _ => False
    end%I
  with
  t_ty (T1 T2: ty) {struct T1}: iProp Σ :=
    match (T1, T2) with
    | (TTop, TTop) => True
    | (TBot, TBot) => True
    | (TAnd T11 T12, TAnd T21 T22) =>
      t_ty T11 T21 ∧ t_ty T12 T22
    | (TOr T11 T12, TOr T21 T22) =>
      t_ty T11 T21 ∧ t_ty T12 T22
    | (TLater T1, TLater T2) =>
      t_ty T1 T2
    | (TAll T11 T12, TAll T21 T22) =>
      t_ty T11 T21 ∧ t_ty T12 T22
    | (TMu T1, TMu T2) =>
      t_ty T1 T2
    | (TVMem l1 T1, TVMem l2 T2) => ⌜l1 = l2⌝ ∧ t_ty T1 T2
    | (TTMem l1 T11 T12, TTMem l2 T21 T22) => ⌜l1 = l2⌝ ∧ t_ty T11 T21 ∧ t_ty T12 T22
    | (TSel p1 l1, TSel p2 l2) => t_path p1 p2 ∧ ⌜l1 = l2⌝
    | (TSelA p1 l1 T11 T12, TSelA p2 l2 T21 T22) => t_path p1 p2 ∧ ⌜l1 = l2⌝ ∧ t_ty T11 T21 ∧ t_ty T12 T22
    | (TNat, TNat) => True
    | _ => False
    end%I.


  Lemma 
    t_tm (n: nat) (t1 t2: tm): Prop
    with
    t_vl (n: nat) (t1 t2: vl): Prop.
  Proof.
    destruct t1 eqn:Heq1; destruct t2 eqn: Heqn2.

End translation.
