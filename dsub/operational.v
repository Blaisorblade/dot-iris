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

(* XXX now duplicated with synLemmas.v *)
(** Let's prove that [nclosed a n → a.|[to_subst (idsσ n)] = a], and ditto for values. *)
Section to_subst_idsσ_is_id.
  Lemma to_subst_map_commute_aux f n x r: x < n → to_subst (map f (idsσ n).|[ren r]) x = f (to_subst (idsσ n).|[ren r] x).
  Proof.
    elim: n r x => [|n IHn] r x Hle; first omega.
    destruct x; first done; asimpl.
    apply IHn; omega.
  Qed.

  Lemma to_subst_map_commute f n x: x < n → to_subst (map f (idsσ n)) x = f (to_subst (idsσ n) x).
  Proof. pose proof (to_subst_map_commute_aux f n x (+0)) as H. asimpl in H. exact H. Qed.

  Arguments push_var /.
  Lemma idsσ_eq_ids n: eq_n_s (to_subst (idsσ n)) ids n.
  Proof.
    induction n => x Hle. by rewrite to_subst_nil.
    destruct x => //=.
    assert (x < n) as Hle' by auto using lt_S_n.
    rewrite to_subst_cons /= to_subst_map_commute // IHn //.
  Qed.

  Lemma closed_subst_idsρ `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A) n :
    nclosed a n → a.|[to_subst (idsσ n)] = a.
  Proof.
    intro Hcl. rewrite (Hcl _ ids); first by asimpl. by apply idsσ_eq_ids.
  Qed.

  Lemma closed_subst_vl_idsρ v n:
    nclosed_vl v n → v.[to_subst (idsσ n)] = v.
  Proof.
    intro Hcl. rewrite (Hcl _ ids); first by asimpl. by apply idsσ_eq_ids.
  Qed.
End to_subst_idsσ_is_id.

(** This is a yet imperfect version of an alternative translation. *)
Section translation.
  Definition stys := gmap stamp ty.
  Implicit Type g: stys.
  Definition unstamp_vstamp g vs s := (default TNat (g !! s)).|[to_subst vs].
  Arguments unstamp_vstamp /.

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
        | vstamp vs s => vty (unstamp_vstamp g vs s)
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
        (* | TTop => T *)
        (* | TBot => T *)
        (* | TAnd T1 T2 => TAnd (go T1) (go T2) *)
        (* | TOr T1 T2 => TOr (go T1) (go T2) *)
        (* | TLater T => TLater (go T) *)
        | TAll T1 T2 => TAll (go T1) (go T2)
        (* | TMu T => TMu (go T) *)
        | TTMem T1 T2 => TTMem (go T1) (go T2)
        | TSel v => TSel (unstamp_vl g v)
        (* | TSelA v T1 T2 => TSelA (unstamp_vl g v) (go T1) (go T2) *)
        | TNat => T
        end
    in go T.

  (* XXX: Not enough, we must also require that e2 contains no concrete types. *)
  Definition stamps_tm e1 g e2 := e1 = unstamp_tm g e2.
  Definition stamps_vl v1 g v2 := v1 = unstamp_vl g v2.
  Definition stamps_ty T1 g T2 := T1 = unstamp_ty g T2.

  Definition emptystys: stys := ∅.

  Definition gdom {X} (g: gmap stamp X) := dom (gset stamp) g.
  Arguments gdom /.

  Lemma fresh_stamp {X} (g: gmap stamp X): ∃ s, s ∉ gdom g.
  Proof. exists (fresh (dom (gset stamp) g)). by apply is_fresh. Qed.

  Lemma fresh_stamp_strong g T: ∃ s, s ∉ dom (gset stamp) g ∧ g ⊆ <[s := T]> g.
  Proof.
    pose proof (fresh_stamp g) as [s Hfresh].
    exists s; split =>//. by eapply insert_subseteq, not_elem_of_dom, Hfresh.
  Qed.

  Lemma fresh_stamp_strong' g T: ∃ s, s ∉ gdom g ∧ gdom g ⊆ gdom (<[s := T]> g).
  Proof.
    pose proof (fresh_stamp_strong g T) as [s []].
    exists s; split =>//=. by apply subseteq_dom.
  Qed.

  (** This lemma suggests this definition is problematic: we don't want empty environments to work.
      They'd fail later lemmas but this is annoying.
      Bigger problem: we should also translate T before storing it in the map! Or after? *)
  Lemma exists_stamped_vty_bad T g: ∃ v' g', stamps_vl (vty T) g' v' ∧ g ⊆ g'.
  Proof.
    pose proof (fresh_stamp_strong g T) as [s []].
    exists (vstamp (idsσ 0) s); rewrite /stamps_vl /unstamp_vl /=; asimpl.
    exists (<[s:=T]> g); by rewrite lookup_insert /=.
  Qed.

  Lemma exists_stamped_vty T n g: nclosed T n → ∃ v' g', stamps_vl (vty T) g' v' ∧ g ⊆ g'.
  Proof.
    pose proof (fresh_stamp_strong g T) as [s []].
    exists (vstamp (idsσ n) s); rewrite /stamps_vl /unstamp_vl /=; asimpl.
    exists (<[s:=T]> g); by rewrite lookup_insert closed_subst_idsρ /=.
  Qed.

  (** Only true for really stamped values. *)
  Lemma unstamp_mono_tm g1 g2 t: g1 ⊆ g2 → (unstamp_tm g1 t) = (unstamp_tm g2 t). Admitted.
  Lemma unstamp_mono_vl g1 g2 v: g1 ⊆ g2 → (unstamp_vl g1 v) = (unstamp_vl g2 v). Admitted.
  Lemma unstamp_mono_ty g1 g2 T: g1 ⊆ g2 → (unstamp_ty g1 T) = (unstamp_ty g2 T). Admitted.

  (* The statement isn't quite right yet. This only works for properly
     translated values, and we don't yethave the correct definition. *)
  Lemma
    exists_stamped_vl t g: ∃ t' g', stamps_vl t g' t' ∧ g ⊆ g'
    with
    exists_stamped_tm t g: ∃ t' g', stamps_tm t g' t' ∧ g ⊆ g'
    with
    exists_stamped_ty t g: ∃ t' g', stamps_ty t g' t' ∧ g ⊆ g'.
  Proof.
    all: destruct t eqn:?; rewrite ?/stamps_tm ?/stamps_vl ?/stamps_ty; cbn.
    all: try by (exists t; exists g; subst; cbn).
    all: try match goal with
      | H : context [vstamp _] |- _ => fail 1
      | H : context [vty _] |- _ => fail 1
      | H : ?t = ?c ?t1 ?t2 |- _ =>
        (pose proof (exists_stamped_tm t0_1 g) as (t0_1' & g1 & Hre1 & Hs1) ||
        pose proof (exists_stamped_vl t0_1 g) as (t0_1' & g1 & Hre1 & Hs1) ||
        pose proof (exists_stamped_ty t0_1 g) as (t0_1' & g1 & Hre1 & Hs1));
        (pose proof (exists_stamped_tm t0_2 g1) as (t0_2' & g2 & Hre2 & Hs2) ||
        pose proof (exists_stamped_vl t0_2 g1) as (t0_2' & g2 & Hre2 & Hs2) ||
        pose proof (exists_stamped_ty t0_2 g1) as (t0_2' & g2 & Hre2 & Hs2));
          rewrite Hre1 Hre2 ?(unstamp_mono_tm g1 g2) ?(unstamp_mono_vl g1 g2) ?(unstamp_mono_ty g1 g2) //;
            try (exists (c t0_1' t0_2'); exists g2=>/=; split; by [f_equiv | destruct t0_1'; destruct t0_2' | simplify_order])
      | H : ?t = ?c ?t0_1 |- _ =>
        (pose proof (exists_stamped_tm t0_1 g) as (t0_1' & g1 & Hre1 & Hs1) ||
        pose proof (exists_stamped_vl t0_1 g) as (t0_1' & g1 & Hre1 & Hs1) ||
        pose proof (exists_stamped_ty t0_1 g) as (t0_1' & g1 & Hre1 & Hs1));
          rewrite Hre1;
            try (exists (c t0_1'); exists g1=>/=; by [f_equiv | destruct t0_1'])
      end.
    eapply exists_stamped_vty_bad.
    (* We should make this impossible. *)
    admit.

    (* pose proof (exists_stamped_vl v) as (v' & g3 & Hre3 & Hs3). *)
    (* rewrite Hre3 ?(unstamp_mono_ty g2 g3) //. *)
    (* exists (TSelA v' t0_1' t0_2'). exists g3. *)
    (* split; try by [cbn; f_equiv; destruct t0_1'; destruct t0_2' | simplify_order]. *)
  Admitted.

  Fixpoint t_tm n g (t1 t2: tm) {struct t1}: Prop :=
    match (t1, t2) with
    | (tv v1, tv v2) => t_vl n g v1 v2
    | (tapp t11 t12, tapp t21 t22) =>
      t_tm n g t11 t21 ∧ t_tm n g t12 t22
    | (tskip t1, tskip t2) =>
      t_tm n g t1 t2
    | _ => False
    end
  with
  t_vl n g (v1 v2: vl) {struct v1}: Prop :=
    match (v1, v2) with
    | (var_vl i1, var_vl i2) => i1 = i2
    | (vabs t1, vabs t2) => t_tm (S n) g t1 t2
    | (vnat n1, vnat n2) => n1 = n2
    | (vty T1, vstamp vs s) =>
      (* Needn't we also check that the contents of T1 are syntactic? *)
      nclosed T1 n ∧
      T1 = unstamp_vstamp g vs s
    | _ => False
    end.
  Fixpoint t_ty n g (T1 T2: ty) {struct T1}: Prop :=
    match (T1, T2) with
    (* | (TTop, TTop) => True *)
    (* | (TBot, TBot) => True *)
    (* | (TAnd T11 T12, TAnd T21 T22) => *)
    (*   t_ty n g T11 T21 ∧ t_ty n g T12 T22 *)
    (* | (TOr T11 T12, TOr T21 T22) => *)
    (*   t_ty n g T11 T21 ∧ t_ty n g T12 T22 *)
    (* | (TLater T1, TLater T2) => *)
    (*   t_ty n g T1 T2 *)
    | (TAll T11 T12, TAll T21 T22) =>
      t_ty n g T11 T21 ∧ t_ty (S n) g T12 T22
    (* | (TMu T1, TMu T2) => *)
    (*   t_ty (S n) g T1 T2 *)
    | (TTMem T11 T12, TTMem T21 T22) => t_ty n g T11 T21 ∧ t_ty n g T12 T22
    | (TSel v1, TSel v2) => t_vl n g v1 v2
    (* | (TSelA v1 T11 T12, TSelA v2 T21 T22) => t_vl n g v1 v2 ∧ t_ty n g T11 T21 ∧ t_ty n g T12 T22 *)
    | (TNat, TNat) => True
    | _ => False
    end.

End translation.
