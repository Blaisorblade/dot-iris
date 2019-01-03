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

Require Import DSub.synLemmas.

(** This is a yet imperfect version of an alternative translation. *)
Definition stys := gmap stamp ty.
Implicit Type g: stys.

(* Section translation. *)

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

Definition unstamp_vstamp g vs s := (from_option vty (vstamp vs s) (g !! s)).[to_subst vs].
Arguments unstamp_vstamp /.

Fixpoint unstamp_tm g (t: tm): tm :=
  match t with
  | tv v => tv (unstamp_vl g v)
  | tapp t1 t2 => tapp (unstamp_tm g t1) (unstamp_tm g t2)
  | tskip t => tskip (unstamp_tm g t)
  end
with
unstamp_vl g (v: vl): vl :=
  match v with
  | vstamp vs s => unstamp_vstamp g vs s
  | vabs t => vabs (unstamp_tm g t)
  | vty T => vty (unstamp_ty g T)
  | vnat _ => v
  | var_vl _ => v
  end
with
unstamp_ty g (T: ty): ty :=
  match T with
  (* | TTop => T *)
  (* | TBot => T *)
  (* | TAnd T1 T2 => TAnd (unstamp_ty g T1) (unstamp_ty g T2) *)
  (* | TOr T1 T2 => TOr (unstamp_ty g T1) (unstamp_ty g T2) *)
  (* | TLater T => TLater (unstamp_ty g T) *)
  | TAll T1 T2 => TAll (unstamp_ty g T1) (unstamp_ty g T2)
  (* | TMu T => TMu (unstamp_ty g T) *)
  | TTMem T1 T2 => TTMem (unstamp_ty g T1) (unstamp_ty g T2)
  | TSel v => TSel (unstamp_vl g v)
  (* | TSelA v T1 T2 => TSelA (unstamp_vl g v) (unstamp_ty g T1) (unstamp_ty g T2) *)
  | TNat => T
  end.
(* End translation. *)

Set Primitive Projections.
Module TraversalV2.
  Record Traversal {travStateT: Type} :=
    {
      upS: travStateT → travStateT;
      varP: travStateT → nat → Prop;
      vtyP: travStateT → ty → Prop;
      vstampP: travStateT → vls → stamp → Prop;
    }.
  Global Arguments Traversal _: clear implicits.

  Definition is_unstamped_trav: Traversal unit :=
    {|
      upS := id;
      varP := λ s n, True;
      vtyP := λ s T, True;
      vstampP := λ s vs s, False;
    |}.

  Definition is_stamped_trav: Traversal (nat * stys) :=
    {|
      upS := λ '(n, g), (S n, g);
      varP := λ ts n, True;
      vtyP := λ ts T, False;
      vstampP := λ '(n, g) vs s, length vs = n ∧ ∃ T, g !! s = Some T ∧ nclosed T n;
    |}.

  Section fold.
    Context `(trav: Traversal travStateT).

    Inductive forall_traversal_vl: travStateT → vl → Prop :=
      | trav_var_vl ts i: trav.(varP) ts i → forall_traversal_vl ts (var_vl i)
      | trav_vabs ts t: forall_traversal_tm (trav.(upS) ts) t →
                           forall_traversal_vl ts (vabs t)
      | trav_vnat ts n: forall_traversal_vl ts (vnat n)
      | trav_vty ts T:
          forall_traversal_ty ts T →
          trav.(vtyP) ts T →
          forall_traversal_vl ts (vty T)
      | trav_vstamp ts vs s:
            trav.(vstampP) ts vs s →
            (* This is weird, but apparently we get away without checking that
               these values are syntactic. *)
            (* Forall (forall_traversal_vl ts) vs → *)
            forall_traversal_vl ts (vstamp vs s)
    with
    forall_traversal_tm: travStateT → tm → Prop :=
    | trav_tv ts v: forall_traversal_vl ts v → forall_traversal_tm ts (tv v)
    | trav_tapp ts t1 t2:
        forall_traversal_tm ts t1 →
        forall_traversal_tm ts t2 →
        forall_traversal_tm ts (tapp t1 t2)
    | trav_tskip ts t:
        forall_traversal_tm ts t →
        forall_traversal_tm ts (tskip t)
    with
    forall_traversal_ty: travStateT → ty → Prop :=
    | trav_TAll ts T1 T2:
        forall_traversal_ty ts T1 →
        forall_traversal_ty (trav.(upS) ts) T2 →
        forall_traversal_ty ts (TAll T1 T2)
    | trav_TMem ts T1 T2:
        forall_traversal_ty ts T1 →
        forall_traversal_ty ts T2 →
        forall_traversal_ty ts (TTMem T1 T2)
    | trav_TSel ts v:
        forall_traversal_vl ts v →
        forall_traversal_ty ts (TSel v)
    | trav_TNat ts: forall_traversal_ty ts TNat
      .
  End fold.

  Notation is_unstamped_tm := (forall_traversal_tm is_unstamped_trav ()).
  Notation is_unstamped_vl := (forall_traversal_vl is_unstamped_trav ()).
  Notation is_unstamped_ty := (forall_traversal_ty is_unstamped_trav ()).
  Notation is_stamped_tm n g := (forall_traversal_tm is_stamped_trav (n, g)).
  Notation is_stamped_vl n g := (forall_traversal_vl is_stamped_trav (n, g)).
  Notation is_stamped_ty n g := (forall_traversal_ty is_stamped_trav (n, g)).

  Check (is_unstamped_tm: tm → Prop).

  Global Arguments upS /.
  Global Arguments varP /.
  Global Arguments vtyP /.
  Global Arguments vstampP /.

  Definition is_stamped_gmap g: Prop := ∀ s T, g !! s = Some T → ∃ n, is_stamped_ty n g T.

  Notation stamps_tm n e__u g e__s := (unstamp_tm g e__s = e__u ∧ is_unstamped_tm e__u ∧ is_stamped_tm n g e__s).
  Notation stamps_vl n v__u g v__s := (unstamp_vl g v__s = v__u ∧ is_unstamped_vl v__u ∧ is_stamped_vl n g v__s).
  Notation stamps_ty n T__u g T__s := (unstamp_ty g T__s = T__u ∧ is_unstamped_ty T__u ∧ is_stamped_ty n g T__s).

  Lemma stamped_idsσ_ren g m n r: Forall (is_stamped_vl m g) (idsσ n).|[ren r].
  Proof.
    elim: n m r => [|n IHn] m r //=.
    repeat constructor => //=. asimpl. apply IHn.
  Qed.

  Hint Constructors forall_traversal_vl forall_traversal_ty forall_traversal_tm.

  (* Unused. *)
  (* Lemma stamped_idsσ g m n: Forall (is_stamped_vl m g) (idsσ n). *)
  (* Proof. pose proof (stamped_idsσ_ren g m n (+0)) as H. by asimpl in H. Qed. *)

  (* Core cases of existence of translations. *)
  Lemma exists_stamped_vty T n g: is_unstamped_vl (vty T) → nclosed_vl (vty T) n → ∃ v' g', stamps_vl n (vty T) g' v' ∧ g ⊆ g'.
  (* Lemma exists_stamped_vty T n g: is_unstamped_ty T → nclosed T n → ∃ v' g', stamps_vl n (vty T) g' v' ∧ g ⊆ g'. *)
  Proof.
    intros Hus Hcl.
    pose proof (fresh_stamp_strong g T) as [s []].
    exists (vstamp (idsσ n) s); rewrite /=; asimpl.
    exists (<[s:=T]> g).
    have: nclosed T n. by move: Hcl; solve_inv_fv_congruence.
    repeat (econstructor; rewrite ?lookup_insert ?closed_subst_idsρ ?length_idsσ /=) => //.
      (* [|apply stamped_idsσ]. *)
  Qed.

  Lemma exists_stamped_vstamp vs s n g: is_unstamped_vl (vstamp vs s) → nclosed_vl (vstamp vs s) n → ∃ v' g', stamps_vl n (vstamp vs s) g' v' ∧ g ⊆ g'.
  Proof. by inversion 1. Qed.

  Lemma not_stamped_vty g n T:
    ¬ (is_stamped_vl n g (vty T)).
  Proof. by inversion 1. Qed.

  Lemma is_stamped_vty_mono g1 g2 n T:
    g1 ⊆ g2 →
    is_stamped_vl n g1 (vty T) →
    is_stamped_vl n g2 (vty T).
  Proof. intros; exfalso. by eapply not_stamped_vty. Qed.

  Lemma is_stamped_vstamp_mono g1 g2 n s vs:
    g1 ⊆ g2 →
    is_stamped_vl n g1 (vstamp vs s) →
    is_stamped_vl n g2 (vstamp vs s).
  Proof.
    inversion 2; subst; simpl in *; ev.
    repeat econstructor => //=. by eapply map_subseteq_spec.
  Qed.

  Fixpoint is_stamped_mono_tm g1 g2 n e__s {struct e__s}:
    g1 ⊆ g2 →
    is_stamped_tm n g1 e__s →
    is_stamped_tm n g2 e__s
  with is_stamped_mono_vl g1 g2 n v__s {struct v__s}:
    g1 ⊆ g2 →
    is_stamped_vl n g1 v__s →
    is_stamped_vl n g2 v__s
  with is_stamped_mono_ty g1 g2 n T__s {struct T__s}:
    g1 ⊆ g2 →
    is_stamped_ty n g1 T__s →
    is_stamped_ty n g2 T__s.
  Proof.
    all:
      intros Hg Hs; [> destruct e__s | destruct v__s | destruct T__s ]; inverse Hs;
      try eapply is_stamped_vstamp_mono => //;
      constructor => //; by [eapply is_stamped_mono_vl | eapply is_stamped_mono_tm | eapply is_stamped_mono_ty].
  Qed.

  Lemma stamps_unstamp_vstamp_mono g1 g2 n v__u vs s:
    g1 ⊆ g2 →
    stamps_vl n v__u g1 (vstamp vs s) →
    unstamp_vl g2 (vstamp vs s) = v__u.
  Proof.
    intros Hg (Huns & _ & Hs).
    assert (∃ T, g1 !! s = Some T) as [T__s Hlook1]. by inverse Hs; cbn in *; ev; econstructor.
    assert (g2 !! s = Some T__s) as Hlook2. by eapply map_subseteq_spec.
    move: Huns. by rewrite /= Hlook1 Hlook2.
  Qed.

  Fixpoint stamps_unstamp_mono_tm g1 g2 n e__u e__s {struct e__s}: g1 ⊆ g2 →
                                     stamps_tm n e__u g1 e__s →
                                     unstamp_tm g2 e__s = e__u
  with stamps_unstamp_mono_vl g1 g2 n v__u (v__s: vl) {struct v__s}: g1 ⊆ g2 →
                                    stamps_vl n v__u g1 v__s →
                                    unstamp_vl g2 v__s = v__u
  with stamps_unstamp_mono_ty g1 g2 n T__u T__s {struct T__s}: g1 ⊆ g2 →
                                    stamps_ty n T__u g1 T__s →
                                    unstamp_ty g2 T__s = T__u.
  Proof.
    all: intros Hg (Hus & Hu & Hs); revert n Hs Hu Hus;
        [> revert e__u; induction e__s | revert v__u; induction v__s | revert T__u; induction T__s]; intros;
    try (by eapply stamps_unstamp_vstamp_mono) || cbn in Hus |- *; inverse Hs; inverse Hu; f_equal;
    by [eauto | eapply stamps_unstamp_mono_vl | eapply stamps_unstamp_mono_tm].
  Qed.

  Lemma stamps_mono_tm g1 g2 n e__u e__s: g1 ⊆ g2 →
                                     stamps_tm n e__u g1 e__s →
                                     stamps_tm n e__u g2 e__s
  with stamps_mono_vl g1 g2 n v__u v__s: g1 ⊆ g2 →
                                    stamps_vl n v__u g1 v__s →
                                    stamps_vl n v__u g2 v__s
  with stamps_mono_ty g1 g2 n T__u T__s: g1 ⊆ g2 →
                                    stamps_ty n T__u g1 T__s →
                                    stamps_ty n T__u g2 T__s.
  Proof.
    all: intros Hg Hs; destruct_and! ; repeat split;
      eauto using stamps_unstamp_mono_vl, stamps_unstamp_mono_ty, stamps_unstamp_mono_tm,
        is_stamped_mono_vl, is_stamped_mono_tm, is_stamped_mono_ty.
  Qed.

  Ltac pick_lemma lty ltm lvl trm tac :=
    let L := match type of trm with | ty => lty | tm => ltm | vl => lvl end
    in tac L.
  Ltac pick_stamps_unstamp_mono :=
    pick_lemma constr:(stamps_unstamp_mono_ty) constr:(stamps_unstamp_mono_tm) constr:(stamps_unstamp_mono_vl).
  Ltac pick_is_stamped_mono :=
    pick_lemma constr:(is_stamped_mono_ty) constr:(is_stamped_mono_tm) constr:(is_stamped_mono_vl).

  Fixpoint exists_stamped_vl t__u g1 n {struct t__u}: is_unstamped_vl t__u → nclosed_vl t__u n → ∃ t__s g2, stamps_vl n t__u g2 t__s ∧ g1 ⊆ g2
  with exists_stamped_tm t__u g1 n {struct t__u}: is_unstamped_tm t__u → nclosed t__u n → ∃ t__s g2, stamps_tm n t__u g2 t__s ∧ g1 ⊆ g2
  with exists_stamped_ty t__u g1 n {struct t__u}: is_unstamped_ty t__u → nclosed t__u n → ∃ t__s g2, stamps_ty n t__u g2 t__s ∧ g1 ⊆ g2.
  Proof.
    all: intros Hus Hcl; destruct t__u eqn:?; cbn.
    all: (abstract by [exists t__u; exists g1; subst; repeat constructor =>// | eapply exists_stamped_vstamp | eapply exists_stamped_vty]) || inverse Hus.

    all:
      let
        pick_exists_stamped :=
        pick_lemma constr:(exists_stamped_ty) constr:(exists_stamped_tm) constr:(exists_stamped_vl)
      in let
        recurse L t g n Hcl t__s g2 :=
        efeed (L t g n)
              using (fun p => pose proof p as (t__s & g2 & ?))
          by (by [| move: Hcl; solve_inv_fv_congruence])
      in let
        smartRecurse t t__s g1 g2 :=
        pick_exists_stamped t ltac:(fun L =>
                                      recurse L t g1 (S n) Hcl t__s g2 ||
                                      recurse L t g1 n Hcl t__s g2)
      in
      match goal with
      | |- ∃ _ _, (_ ∧ _ ?c ∧ _) ∧ _ =>
        lazymatch c with
        | ?c ?t1 ?t2 =>
          try solve [
                  smartRecurse t1 t__s1 g1 g2;
                  smartRecurse t2 t__s2 g2 g3;
                  ev; exists (c t__s1 t__s2), g3; cbn;
                  pick_stamps_unstamp_mono t1 ltac:(fun L => erewrite (L g2 g3 _ t1) => //);
                    by simplify_order; repeat constructor; f_equal; try done; pick_is_stamped_mono t__s1 ltac:(fun L => eapply (L g2))]
        | ?c ?t1 =>
          try solve [smartRecurse t1 t__s1 g1 g2;
                  ev; exists (c t__s1), g2; repeat constructor => //=; by f_equal]
        end
      end.
  Qed.

End TraversalV2.

Section translation.
  Section fold.
    Record Traversal {travStateT: Type} {resT: Type} :=
      {
        upS: travStateT → travStateT;
        varP: travStateT → nat → resT;
        vtyP: travStateT → ty → resT → resT;
        vstampP: travStateT → vls → list resT → stamp → resT;
        base: resT;
        op: resT → resT → resT;
      }.
    Global Arguments Traversal _ _: clear implicits.
    Context `(trav: Traversal travStateT resT).
    Local Definition opP := trav.(op).
    Infix "++" := opP.

    Fixpoint traverse_vl (ts: travStateT) v: resT :=
      match v with
      | var_vl i => trav.(varP) ts i
      | vabs t => traverse_tm (trav.(upS) ts) t
      | vnat _ => trav.(base)
      | vty T => trav.(vtyP) ts T (traverse_ty ts T)
      | vstamp vs s => trav.(vstampP) ts vs (map (traverse_vl ts) vs) s
      end
    with
    traverse_tm (ts: travStateT) e: resT :=
      match e with
      | tv v => traverse_vl ts v
      | tapp t1 t2 => traverse_tm ts t1 ++ traverse_tm ts t2
      | tskip t => traverse_tm ts t
      end
    with
    traverse_ty (ts: travStateT) T: resT :=
      match T with
      | TAll T1 T2 => traverse_ty ts T1 ++ traverse_ty (trav.(upS) ts) T2
      | TTMem T1 T2 => traverse_ty ts T1 ++ traverse_ty ts T2
      | TSel v => traverse_vl ts v
      | TNat => trav.(base)
      end.
  End fold.

  Definition is_unstamped_trav: Traversal unit Prop :=
    {|
      upS := id;
      varP := λ s n, True;
      vtyP := λ s T resT, resT;
      vstampP := λ s vs ressVs s, False;
      base := True;
      op := and
    |}.
  Arguments traverse_tm {_} {_} _ _ _: assert.
  Arguments traverse_ty {_} {_} _ _ _: assert.
  Arguments traverse_vl {_} {_} _ _ _: assert.
  Definition is_unstamped_tm := traverse_tm is_unstamped_trav ().
  Definition is_unstamped_vl := traverse_vl is_unstamped_trav ().
  Definition is_unstamped_ty := traverse_ty is_unstamped_trav ().
  Check (is_unstamped_tm: tm → Prop).

  Program Definition is_stamped_trav: Traversal (nat * stys) Prop :=
    {|
      upS := λ '(n, g), (S n, g);
      varP := λ ts n, True;
      vtyP := λ ts T resT, False;
      vstampP := λ '(n, g) vs ressVs s, length vs = n ∧ ∃ T, g !! s = Some T ∧ nclosed T n;
      (* XXX: Here too, it seems we get away without checking this. *)
      (* ∧ Forall ressVs (λ x, x) *)
      base := True;
      op := and
    |}.
  (* Beware, the above cannot check that the looked-up types are stamped. Check that separately! *)
  Definition is_stamped_tm := uncurry (traverse_tm is_stamped_trav).
  Definition is_stamped_vl := uncurry (traverse_vl is_stamped_trav).
  Definition is_stamped_ty := uncurry (traverse_ty is_stamped_trav).
  Check (is_stamped_tm: nat → stys → tm → Prop).

  Definition is_stamped_gmap g: Prop := ∀ s T, g !! s = Some T → ∃ n, is_stamped_ty n g T.

  Definition stamps_tm n e__u g e__s := unstamp_tm g e__s = e__u ∧ is_unstamped_tm e__u ∧ is_stamped_tm n g e__s.
  Definition stamps_vl n v__u g v__s := unstamp_vl g v__s = v__u ∧ is_unstamped_vl v__u ∧ is_stamped_vl n g v__s.
  Definition stamps_ty n T__u g T__s := unstamp_ty g T__s = T__u ∧ is_unstamped_ty T__u ∧ is_stamped_ty n g T__s.

  (** This lemma suggests this definition is problematic: we don't want empty environments to work.
      They'd fail later lemmas but this is annoying.
      Bigger problem: we should also translate T before storing it in the map! Or after? *)
  Lemma exists_stamped_vty T n g: is_unstamped_ty T → nclosed T n → ∃ v' g', stamps_vl n (vty T) g' v' ∧ g ⊆ g'.
  Proof.
    intros Hunst Hcl.
    pose proof (fresh_stamp_strong g T) as [s []].
    exists (vstamp (idsσ n) s); rewrite /stamps_vl /unstamp_vl /=; asimpl.
    exists (<[s:=T]> g); rewrite lookup_insert /= closed_subst_idsρ // length_idsσ.
    repeat split; eauto.
  Qed.

  (* Lemma exists_stamped_vty_bad T g (n: nat): is_unstamped_ty T → ∃ v' g', stamps_vl 0 (vty T) g' v' ∧ g ⊆ g'. *)
  (* Proof. *)
  (*   pose proof (fresh_stamp_strong g T) as [s []]. *)
  (*   exists (vstamp (idsσ 0) s); rewrite /stamps_vl /unstamp_vl /=; asimpl. *)
  (*   exists (<[s:=T]> g); rewrite lookup_insert //=; repeat esplit; eauto. *)
  (* Fail Qed. *)
  (* Abort. *)
  Lemma not_stamped_vty g n T:
    is_stamped_vl n g (vty T) → False.
  Proof. trivial. Qed.

  Lemma is_stamped_vty_mono g1 g2 n T:
    g1 ⊆ g2 →
    is_stamped_vl n g1 (vty T) →
    is_stamped_vl n g2 (vty T).
  Proof. intros; exfalso. by eapply not_stamped_vty. Qed.

  Lemma is_stamped_vstamp_mono g1 g2 n s vs:
    g1 ⊆ g2 →
    is_stamped_vl n g1 (vstamp vs s) →
    is_stamped_vl n g2 (vstamp vs s).
  Proof.
    (* intros Hg (Hl & T & Hlook & Hcl). *)
    cbn; intros; ev.
    repeat esplit => //. by eapply map_subseteq_spec.
  Qed.

  Arguments is_stamped_vl _ _ !_ /.
  Arguments is_stamped_ty _ _ !_ /.
  Arguments is_stamped_tm _ _ !_ /.
  Arguments prod_uncurry _ _ _ /.
  Arguments traverse_vl _ _ _: simpl nomatch.
  Arguments traverse_tm _ _ _: simpl nomatch.
  Arguments traverse_ty _ _ _: simpl nomatch.
  Arguments upS /.

  Lemma
    is_stamped_mono_tm g1 g2 n e__s:
    g1 ⊆ g2 →
    is_stamped_tm n g1 e__s →
    is_stamped_tm n g2 e__s
  with
  is_stamped_mono_vl g1 g2 n v__s:
    g1 ⊆ g2 →
    is_stamped_vl n g1 v__s →
    is_stamped_vl n g2 v__s
  with
  is_stamped_mono_ty g1 g2 n T__s:
    g1 ⊆ g2 →
    is_stamped_ty n g1 T__s →
    is_stamped_ty n g2 T__s.
  Proof.
    Ltac induct n t__s := intros Hg; revert n; induction t__s; intros n0 Hs; cbn in Hs |- *.
    - induct n e__s; ev; repeat split_and; by eapply is_stamped_mono_vl || eauto.
    - induct n v__s; by eapply is_stamped_vstamp_mono || eapply is_stamped_mono_tm || eauto.
    - induct n T__s; ev; repeat split_and; by eapply is_stamped_mono_vl || eauto || apply IHT__s2.
  Qed.
  (* That worked, but a mutual induction principle might be more robust... however, beware the lists!
     Write it by hand? *)

  Lemma stamps_unstamp_vstamp_mono g1 g2 n v__u vs s:
    g1 ⊆ g2 →
    stamps_vl n v__u g1 (vstamp vs s) →
    unstamp_vl g2 (vstamp vs s) = v__u.
  Proof.
    intros Hg (Huns & _ & _ & T & Hlook1 & _). move: Huns.
    assert (g2 !! s = Some T) as Hlook2. by eapply map_subseteq_spec.
    by rewrite /= Hlook1 Hlook2.
  Qed.

  Fixpoint stamps_unstamp_mono_tm g1 g2 n e__u e__s: g1 ⊆ g2 →
                                     stamps_tm n e__u g1 e__s →
                                     unstamp_tm g2 e__s = e__u
  with stamps_unstamp_mono_vl g1 g2 n v__u (v__s: vl)  {struct v__s}: g1 ⊆ g2 →
                                    stamps_vl n v__u g1 v__s →
                                    unstamp_vl g2 v__s = v__u
  with stamps_unstamp_mono_ty g1 g2 n T__u T__s: g1 ⊆ g2 →
                                    stamps_ty n T__u g1 T__s →
                                    unstamp_ty g2 T__s = T__u.
  Proof.
    all: rewrite /stamps_ty /stamps_vl /stamps_tm;
      intros Hg (Hus & Hu & Hs).
    - revert n e__u Hs Hu Hus. induction e__s; intros; cbn in Hus |- *;
        subst; cbn in *; f_equal; ev; try eauto || by eapply (stamps_unstamp_mono_vl _ _ _ _ v).
    - revert n v__u Hs Hu Hus; induction v__s; intros;
        try (by eapply stamps_unstamp_vstamp_mono);
        cbn in Hus |- *;
        subst; cbn in *; f_equal; ev; try done.
      erewrite stamps_unstamp_mono_tm => //.
    - revert n T__u Hs Hu Hus. induction T__s; intros; cbn in Hus |- *;
        subst; cbn in *; f_equal; ev;
          try eauto || by eapply stamps_unstamp_mono_vl || done.
  Qed.

  Lemma stamps_mono_tm g1 g2 n e__u e__s: g1 ⊆ g2 →
                                     stamps_tm n e__u g1 e__s →
                                     stamps_tm n e__u g2 e__s
  with stamps_mono_vl g1 g2 n v__u v__s: g1 ⊆ g2 →
                                    stamps_vl n v__u g1 v__s →
                                    stamps_vl n v__u g2 v__s
  with stamps_mono_ty g1 g2 n T__u T__s: g1 ⊆ g2 →
                                    stamps_ty n T__u g1 T__s →
                                    stamps_ty n T__u g2 T__s.
  Proof.
    all: intros Hg Hs; ev; repeat split;
      eauto using stamps_unstamp_mono_vl, stamps_unstamp_mono_ty, stamps_unstamp_mono_tm;
      rewrite /stamps_ty /stamps_vl /stamps_tm in Hs; ev; eauto using is_stamped_mono_vl, is_stamped_mono_tm, is_stamped_mono_ty.
  Qed.

End translation.
