(** Define "stamping" (what we used to call translation) in a purely syntactic
    way, without involving Iris. *)
From stdpp Require Import gmap.
From D Require Import tactics.
From D.DSub Require Import syn syn_lemmas type_extraction_syn core_stamping_defs.

Set Implicit Arguments.

Implicit Types (T: ty) (v: vl) (e: tm) (Γ : ctx) (g: stys) (n: nat).

Lemma is_stamped_tm_skip i T g n e:
  is_stamped_tm i g e →
  is_stamped_tm i g (iterate tskip n e).
Proof. elim: n e => [//|n IHn] e Hs. constructor; exact: IHn. Qed.

(** Here we do not unstamp types from the map, and we can't: unstamping the map
    recursively might not be terminate. We need an unstamped map, which is
    what's produced in the first pass.
    However, this problem disappears because paths are just source variables, not values.
 *)
Definition unstamp_vstamp g vs s := (from_option vty (vstamp vs s) (g !! s)).[∞ vs].
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
  | vint _ => v
  | var_vl _ => v
  end
with
unstamp_ty g (T: ty): ty :=
  match T with
  | TTop => T
  | TBot => T
  (* | TAnd T1 T2 => TAnd (unstamp_ty g T1) (unstamp_ty g T2) *)
  (* | TOr T1 T2 => TOr (unstamp_ty g T1) (unstamp_ty g T2) *)
  | TLater T => TLater (unstamp_ty g T)
  | TAll T1 T2 => TAll (unstamp_ty g T1) (unstamp_ty g T2)
  (* | TMu T => TMu (unstamp_ty g T) *)
  | TTMem T1 T2 => TTMem (unstamp_ty g T1) (unstamp_ty g T2)
  | TSel v => TSel (unstamp_vl g v)
  | TInt => T
  end.

Notation stamps_tm n e__u g e__s := (unstamp_tm g e__s = e__u ∧ is_unstamped_tm e__u ∧ is_stamped_tm n g e__s).
Notation stamps_vl n v__u g v__s := (unstamp_vl g v__s = v__u ∧ is_unstamped_vl v__u ∧ is_stamped_vl n g v__s).
Notation stamps_ty n T__u g T__s := (unstamp_ty g T__s = T__u ∧ is_unstamped_ty T__u ∧ is_stamped_ty n g T__s).

(* Core cases of existence of translations. *)
Definition stamp_vty g n T :=
  let '(g', (s, σ)) := (extract g n T) in
  (vstamp σ s, g').

(** Unstamped types are already stamped, because they can't contain type
    definitions to stamp. *)
Lemma unstamped_stamped_type T g n:
  is_unstamped_ty T →
  nclosed T n →
  is_stamped_ty n g T.
Proof.
  move => Hus; move: n. induction T => n Hcl; inverse Hus; cbn in *; constructor => //=.
  all: try by (eapply IHT || eapply IHT1 || eapply IHT2; eauto 2; auto with fv).
  ev; simplify_eq; constructor. rewrite /= -nclosed_vl_ids_equiv. auto with fv.
Qed.
Arguments extraction: simpl never.
Import traversals.Trav1.

Lemma stamp_vty_spec {T n} g:
  is_unstamped_vl (vty T) → nclosed T n →
  let '(g', (s, σ)) := (extract g n T) in
  let v' := (vstamp σ s) in
  stamps_vl n (vty T) g' v' ∧ g ⊆ g' ∧
    T ~[ n ] (g', (s, σ)).
Proof.
  intros Hus Hcl.
  inverse Hus.
  have Hext: T ~[ n ] (extract g n T)
    by apply /extract_spec /unstamped_stamped_type.
  destruct (extract g n T) as (g' & s & σ) eqn:Heq.
  rewrite /extract in Heq; simplify_eq.
  split_and!; try eapply trav_vstamp with (T' := T) (ts' := (n, <[fresh_stamp g := T]> g));
    rewrite /= ?lookup_insert //= ?closed_subst_idsρ ?length_idsσ //;
    eauto using is_stamped_idsσ, unstamped_stamped_type.
Qed.

Lemma exists_stamped_vty T n g:
  is_unstamped_vl (vty T) → nclosed_vl (vty T) n →
  { v' & { g' | stamps_vl n (vty T) g' v' ∧ g ⊆ g' } }.
Proof.
  intros Hus Hclv. destruct (stamp_vty g n T) as (v', g') eqn:?.
  have HclT: nclosed T n. by solve_inv_fv_congruence_h Hclv.
  edestruct (stamp_vty_spec g Hus HclT); cbn in *.
  exists v', g'; simplify_eq; eauto.
Qed.

Lemma var_stamps_to_self1 g x v: unstamp_vl g v = var_vl x → v = var_vl x.
Proof. case: v => //= σ s. move: (g!!s) => [T|] /= Heq; simplify_eq. Qed.

Lemma stamps_tm_skip n g i e e':
  stamps_tm n e g e' →
  stamps_tm n (iterate tskip i e) g (iterate tskip i e').
Proof.
  move => [Heq [Hus Hs]]. elim: i => [//|] i [IHeq [IHus IHs]].
  rewrite !iterate_S /=. split_and!; by [constructor| f_equiv].
Qed.
Hint Resolve stamps_tm_skip : core.

Lemma exists_stamped_vstamp vs s n g: is_unstamped_vl (vstamp vs s) → nclosed_vl (vstamp vs s) n → { v' & { g' | stamps_vl n (vstamp vs s) g' v' ∧ g ⊆ g' } }.
Proof. intro H. exfalso. by inversion H. Qed.

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

Lemma stamps_unstamp_mono_mut:
  (∀ e__s g1 g2 n e__u, g1 ⊆ g2 →
                    stamps_tm n e__u g1 e__s →
                    unstamp_tm g2 e__s = e__u) ∧
  (∀ v__s g1 g2 n v__u, g1 ⊆ g2 →
                    stamps_vl n v__u g1 v__s →
                    unstamp_vl g2 v__s = v__u) ∧
  (∀ T__s g1 g2 n T__u, g1 ⊆ g2 →
                    stamps_ty n T__u g1 T__s →
                    unstamp_ty g2 T__s = T__u).
Proof.
  apply syntax_mut_ind; intros; ev; try (exact: stamps_unstamp_vstamp_mono);
    with_is_stamped inverse; with_is_unstamped inverse;
    naive_solver eauto with f_equal.
Qed.

Lemma stamps_unstamp_mono_tm e__s g1 g2 n e__u: g1 ⊆ g2 →
                                    stamps_tm n e__u g1 e__s →
                                    unstamp_tm g2 e__s = e__u.
Proof. apply stamps_unstamp_mono_mut. Qed.

Lemma stamps_unstamp_mono_vl (v__s: vl) g1 g2 n v__u : g1 ⊆ g2 →
                                  stamps_vl n v__u g1 v__s →
                                  unstamp_vl g2 v__s = v__u.
Proof. apply stamps_unstamp_mono_mut. Qed.
Lemma stamps_unstamp_mono_ty T__s g1 g2 n T__u : g1 ⊆ g2 →
                                  stamps_ty n T__u g1 T__s →
                                  unstamp_ty g2 T__s = T__u.
Proof. apply stamps_unstamp_mono_mut. Qed.

Ltac pick_lemma lty ltm lvl trm tac :=
  let L := match type of trm with | ty => lty | tm => ltm | vl_ => lvl end
  in tac L.
Ltac pick_stamps_unstamp_mono :=
  pick_lemma constr:(stamps_unstamp_mono_ty) constr:(stamps_unstamp_mono_tm) constr:(stamps_unstamp_mono_vl).
Ltac pick_is_stamped_mono :=
  pick_lemma constr:(is_stamped_mono_ty) constr:(is_stamped_mono_tm) constr:(is_stamped_mono_vl).
Ltac pick_nclosed :=
  pick_lemma uconstr:(nclosed) uconstr:(nclosed) uconstr:(nclosed_vl).
Ltac assert_closed n t Hcl :=
  pick_nclosed t ltac:(fun D => assert (D t n) by (move: Hcl; solve_inv_fv_congruence)).
Ltac with_freevars n t Hcl tac :=
  (assert_closed n t Hcl; tac n) || (assert_closed (S n) t Hcl; tac (S n)).
(* Maybe it'd be better to write the translation as a plain recursive function. *)

Fixpoint exists_stamped_vl t__u g1 n {struct t__u}: is_unstamped_vl t__u → nclosed_vl t__u n → { t__s & { g2 | stamps_vl n t__u g2 t__s ∧ g1 ⊆ g2 } }
with exists_stamped_tm t__u g1 n {struct t__u}: is_unstamped_tm t__u → nclosed t__u n → { t__s & { g2 | stamps_tm n t__u g2 t__s ∧ g1 ⊆ g2 } }
with exists_stamped_ty t__u g1 n {struct t__u}: is_unstamped_ty t__u → nclosed t__u n → { t__s & { g2 | stamps_ty n t__u g2 t__s ∧ g1 ⊆ g2 } }.
Proof.
  all: intros Hus Hcl; destruct t__u eqn:?; cbn.
  all: try (abstract by [exists t__u; exists g1; subst; repeat constructor =>// | eapply exists_stamped_vstamp | eapply exists_stamped_vty]).
  all:
    let
      pick_exists_stamped :=
      pick_lemma constr:(exists_stamped_ty) constr:(exists_stamped_tm) constr:(exists_stamped_vl)
    in let
      recurse L t g n t__s g2 :=
      efeed (L t g n)
            using (fun p => pose proof p as (t__s & g2 & ?))
        by (by [ | inverse Hus ])
    in let
      smartRecurse t t__s g1 g2 :=
      with_freevars n t Hcl
                    ltac:(fun n' =>
                            pick_exists_stamped t ltac:(fun L => recurse L t g1 n' t__s g2))
    in
    match goal with
    | |- { _ & { _ | (_ ∧ _ ?c ∧ _) ∧ _ } } =>
      lazymatch c with
      | ?c ?t1 ?t2 =>
        try solve [
                smartRecurse t1 t__s1 g1 g2;
                smartRecurse t2 t__s2 g2 g3;
                ev; exists (c t__s1 t__s2), g3; inversion Hus; cbn;
                pick_stamps_unstamp_mono t1
                  ltac:(fun L => erewrite (L _ g2 g3 _ t1) => //);
                simplify_order; repeat constructor; f_equal;
                by [| pick_is_stamped_mono t__s1 ltac:(fun L => eapply (L g2))]]
      | ?c ?t1 =>
        try solve [smartRecurse t1 t__s1 g1 g2; ev; exists (c t__s1), g2;
                    inverse Hus; repeat constructor; by [|f_equal/=]]
      end
    end.
  all: exists t__u, g1; subst; repeat constructor; eauto using nclosed_var_lt.
Qed.
