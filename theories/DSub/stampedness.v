(** Define "stamping" (what we used to call translation) in a purely syntactic
    way, without involving Iris. *)
From stdpp Require Import gmap list.
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
    varP := λ '(n, g) i, i < n;
    vtyP := λ ts T, False;
    vstampP := λ '(n, g) vs s, ∃ T', g !! s = Some T' ∧ nclosed T' (length vs);
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
          Forall (forall_traversal_vl ts) vs →
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
  | trav_TTop ts: forall_traversal_ty ts TTop
  | trav_TBot ts: forall_traversal_ty ts TBot
  | trav_TLater ts T1:
      forall_traversal_ty ts T1 →
      forall_traversal_ty ts (TLater T1)
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

Lemma is_stamped_idsσ_ren g m n j: j + n <= m → Forall (is_stamped_vl m g) (idsσ n).|[ren (+j)].
Proof.
  elim: n m j => [|n IHn] m j Ijm //=.
  repeat constructor => //=; first lia.
  asimpl; apply IHn; lia.
Qed.

Lemma is_stamped_idsσ g m n: n <= m → Forall (is_stamped_vl m g) (idsσ n).
Proof. pose proof (@is_stamped_idsσ_ren g m n 0) as H. asimpl in H. exact: H. Qed.

Hint Constructors forall_traversal_vl forall_traversal_ty forall_traversal_tm.

Lemma not_stamped_vty g n T:
  ¬ (is_stamped_vl n g (vty T)).
Proof. by inversion 1. Qed.

Lemma is_stamped_vty_mono g1 g2 n T:
  g1 ⊆ g2 →
  is_stamped_vl n g1 (vty T) →
  is_stamped_vl n g2 (vty T).
Proof. intros; exfalso. by eapply not_stamped_vty. Qed.

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
  apply syntax_mut_ind;
    try by [ intros; with_is_stamped inverse; constructor; cbn in *; eauto].
  - move => vs s IHvs g1 g2 n Hg Hstg1.
    inversion Hstg1; subst. cbn in *; ev.
    repeat econstructor => //=. by eapply map_subseteq_spec.
    decompose_Forall; eauto.
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

(* XXX Still used? *)
Lemma is_stamped_vstamp_mono g1 g2 n s vs:
  g1 ⊆ g2 →
  is_stamped_vl n g1 (vstamp vs s) →
  is_stamped_vl n g2 (vstamp vs s).
Proof. apply is_stamped_mono_vl. Qed.

Definition is_stamped_sub n m g s :=
  ∀ i, i < n → is_stamped_vl m g (s i).
Definition is_stamped_ren n m g r := is_stamped_sub n m g (ren r).

Lemma is_stamped_ren_shift n m j g:
  m >= j + n → is_stamped_ren n m g (+j).
Proof. constructor => //=; lia. Qed.

Lemma is_stamped_ren_up n m g r:
  is_stamped_ren n m g r →
  is_stamped_ren (S n) (S m) g (upren r).
Proof.
  (* rewrite /is_stamped_ren /is_stamped_sub /=. *)
  move => Hr [|i] //= Hi; first by constructor => /=; lia.
  have Hi': i < n by lia.
  specialize (Hr i Hi'); inverse Hr.
  constructor; cbn in *; by lia.
Qed.
Hint Resolve is_stamped_ren_up is_stamped_ren_shift.

From D.DSub Require Import closed_subst.

Lemma is_stamped_nclosed_ren i j g r: is_stamped_ren i j g r → nclosed_ren i j r.
Proof.
  move => /= Hr x Hx. specialize (Hr x Hx); inverse Hr. exact: nclosed_vl_ids.
Qed.

Lemma is_stamped_ren_mut:
  (∀ t g r i j,
    is_stamped_ren i j g r →
    is_stamped_tm i g t →
    is_stamped_tm j g (rename r t)) ∧
  (∀ v g r i j,
    is_stamped_ren i j g r →
    is_stamped_vl i g v →
    is_stamped_vl j g (rename r v)) ∧
  (∀ T g r i j,
    is_stamped_ren i j g r →
    is_stamped_ty i g T →
    is_stamped_ty j g (rename r T)).
Proof.
  apply syntax_mut_ind; intros; with_is_stamped ltac:(fun H => inversion_clear H);
    cbn in *; try by [constructor; cbn; eauto].
  - eauto.
  - constructor. rewrite /= /rename /list_rename map_length /=.
    by ev; eexists; split_and!.
    by rewrite Forall_fmap; decompose_Forall; eauto.
Qed.

Lemma is_stamped_ren_vl: ∀ v g r i j,
  is_stamped_ren i j g r →
  is_stamped_vl i g v →
  is_stamped_vl j g (rename r v).
Proof. unmut_lemma is_stamped_ren_mut. Qed.

Lemma is_stamped_sub_up n m g s:
  is_stamped_sub n m g s →
  is_stamped_sub (S n) (S m) g (up s).
Proof.
  move => Hs [|i] Hi //=. by constructor => /=; lia.
  eapply is_stamped_ren_vl; eauto with lia.
Qed.
Hint Resolve is_stamped_sub_up.

Lemma is_stamped_nclosed_mut g:
  (∀ t i,
    is_stamped_tm i g t →
    nclosed t i) ∧
  (∀ v i,
    is_stamped_vl i g v →
    nclosed_vl v i) ∧
  (∀ T i,
    is_stamped_ty i g T →
    nclosed T i).
Proof.
  apply syntax_mut_ind; intros; with_is_stamped inverse => //;
    cbn in *; ev; try (by apply fv_vstamp; decompose_Forall; eauto);
    move => s1 s2 Hseq /=; f_equal.
  (* all: time try firstorder eauto using eq_up. (* 1.7 s *) *)
  (* all: time try naive_solver; eauto using eq_up. (* 0.8s, not all goals. *) *)
  all: try eapply H; try eapply H0; eauto using eq_up.
Qed.

Lemma is_stamped_nclosed_vl v g i:
  is_stamped_vl i g v →
  nclosed_vl v i.
Proof. unmut_lemma (is_stamped_nclosed_mut g). Qed.

Lemma is_stamped_nclosed_ty T g i:
  is_stamped_ty i g T →
  nclosed T i.
Proof. unmut_lemma (is_stamped_nclosed_mut g). Qed.

Lemma is_stamped_nclosed_sub i j g s: is_stamped_sub i j g s → nclosed_sub i j s.
Proof.
  move => /= Hs x Hx. eapply is_stamped_nclosed_vl, (Hs x Hx).
Qed.

Lemma is_stamped_sub_mut:
  (∀ t g s i j,
    is_stamped_sub i j g s →
    is_stamped_tm i g t →
    is_stamped_tm j g t.|[s]) ∧
  (∀ v g s i j,
    is_stamped_sub i j g s →
    is_stamped_vl i g v →
    is_stamped_vl j g v.[s]) ∧
  (∀ T g s i j,
    is_stamped_sub i j g s →
    is_stamped_ty i g T →
    is_stamped_ty j g T.|[s]).
Proof.
  apply syntax_mut_ind; intros; with_is_stamped ltac:(fun H => inversion_clear H);
    cbn in *; try by [constructor; cbn; eauto].
  - eauto.
  - constructor. rewrite /= map_length.
    ev; eexists; split_and!; eauto.
    rewrite Forall_fmap; decompose_Forall; eauto.
Qed.

Lemma is_stamped_sub_vl v g s m n:
  is_stamped_sub n m g s →
  is_stamped_vl n g v →
  is_stamped_vl m g v.[s].
Proof. unmut_lemma is_stamped_sub_mut. Qed.

Lemma is_stamped_sub_ty T g s m n:
  is_stamped_sub n m g s →
  is_stamped_ty n g T →
  is_stamped_ty m g T.|[s].
Proof. unmut_lemma is_stamped_sub_mut. Qed.

Lemma is_stamped_vl_ids g i j: i < j → is_stamped_vl j g (ids i).
Proof. rewrite /ids /Ids_vl; by constructor. Qed.
Hint Resolve is_stamped_vl_ids.

Lemma is_stamped_sub_single n v g:
  is_stamped_vl n g v →
  is_stamped_sub (S n) n g (v .: ids).
Proof. move => Hv [|i] Hin /=; eauto with lia. Qed.

Lemma is_stamped_sub_one n T v g:
  is_stamped_ty (S n) g T →
  is_stamped_vl n g v →
  is_stamped_ty n g (T.|[v/]).
Proof.
  intros; eapply is_stamped_sub_ty => //; by apply is_stamped_sub_single.
Qed.

Lemma is_stamped_sub_rev_mut g:
  (∀ e i,
    nclosed e i →
    ∀ s j,
    is_stamped_tm j g (e.|[s]) →
    is_stamped_tm i g e) ∧
  (∀ v i,
    nclosed_vl v i →
    ∀ s j,
    is_stamped_vl j g (v.[s]) →
    is_stamped_vl i g v) ∧
  (∀ T i,
    nclosed T i →
    ∀ s j,
    is_stamped_ty j g (T.|[s]) →
    is_stamped_ty i g T).
Proof.
  apply nclosed_syntax_mut_ind => /=; intros;
    try by with_is_stamped inverse; ev;
    constructor => /=; eauto using eq_up with lia.

  with_is_stamped inverse; cbn in *; ev.
  unfold hsubst, list_hsubst in *; rewrite -> map_length, @Forall_fmap in *.
  (* move: H8; rewrite /hsubst /list_hsubst Forall_fmap; move => Hstl. *)
  constructor => /=. by eexists; split_and!; eauto.
  by decompose_Forall; eauto.
Qed.

Lemma is_stamped_sub_rev_vl g v s i j:
  nclosed_vl v i →
  is_stamped_vl j g (v.[s]) →
  is_stamped_vl i g v.
Proof. unmut_lemma (is_stamped_sub_rev_mut g). Qed.

Lemma is_stamped_sub_rev_ty g T s i j:
  nclosed T i →
  is_stamped_ty j g (T.|[s]) →
  is_stamped_ty i g T.
Proof. unmut_lemma (is_stamped_sub_rev_mut g). Qed.

Lemma is_stamped_sub_one_rev i T v g:
  nclosed T (S i) →
  is_stamped_ty i g (T.|[v/]) →
  is_stamped_ty (S i) g T.
Proof. intros; by eapply is_stamped_sub_rev_ty. Qed.

Lemma is_stamped_ren_ty i T g:
  nclosed T i →
  is_stamped_ty i g T <->
  is_stamped_ty (S i) g (T.|[ren (+1)]).
Proof.
  have Hs: is_stamped_sub i (S i) g (ren (+1)). by apply is_stamped_ren_shift; lia.
  split; intros; by [ eapply is_stamped_sub_ty | eapply is_stamped_sub_rev_ty].
Qed.
