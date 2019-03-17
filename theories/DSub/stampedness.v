(** Define "stamping" (what we used to call translation) in a purely syntactic
    way, without involving Iris. *)
From stdpp Require Import gmap.
From D Require Import tactics.
From D.DSub Require Import syn operational synLemmas typeExtractionSyn.

Set Primitive Projections.
Set Implicit Arguments.

Implicit Types (T: ty) (v: vl) (e: tm) (Γ : ctx) (g: stys) (n: nat).

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

Global Arguments upS /.
Global Arguments varP /.
Global Arguments vtyP /.
Global Arguments vstampP /.

Lemma stamped_idsσ_ren g m n r: Forall (is_stamped_vl m g) (idsσ n).|[ren r].
Proof.
  elim: n m r => [|n IHn] m r //=.
  repeat constructor => //=. asimpl. apply IHn.
Qed.

Hint Constructors forall_traversal_vl forall_traversal_ty forall_traversal_tm.

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

Ltac with_is_stamped tac :=
  match goal with
    | H: is_stamped_ty _ _ _ |- _ => tac H
    | H: is_stamped_tm _ _ _ |- _ => tac H
    | H: is_stamped_vl _ _ _ |- _ => tac H
  end.

Lemma is_stamped_mono_mut:
  (∀ e__s g1 g2 n,
       g1 ⊆ g2 →
       is_stamped_tm n g1 e__s →
       is_stamped_tm n g2 e__s) ∧
  (∀ v__s g1 g2 n,
      g1 ⊆ g2 →
      is_stamped_vl n g1 v__s →
      is_stamped_vl n g2 v__s) ∧
  (∀ T__s g1 g2 n,
      g1 ⊆ g2 →
      is_stamped_ty n g1 T__s →
      is_stamped_ty n g2 T__s).
Proof.
  apply syntax_mut_ind => *; with_is_stamped inverse;
    by [ eapply is_stamped_vstamp_mono | constructor; cbn in *; eauto].
Qed.

Lemma is_stamped_mono_tm g1 g2 n e__s:
  g1 ⊆ g2 →
  is_stamped_tm n g1 e__s →
  is_stamped_tm n g2 e__s.
Proof. unmut_lemma is_stamped_mono_mut. Qed.
Lemma is_stamped_mono_vl g1 g2 n v__s:
  g1 ⊆ g2 →
  is_stamped_vl n g1 v__s →
  is_stamped_vl n g2 v__s.
Proof. unmut_lemma is_stamped_mono_mut. Qed.
Lemma is_stamped_mono_ty g1 g2 n T__s:
  g1 ⊆ g2 →
  is_stamped_ty n g1 T__s →
  is_stamped_ty n g2 T__s.
Proof. unmut_lemma is_stamped_mono_mut. Qed.
