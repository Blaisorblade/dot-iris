(** Define purely syntactically whether a term is stamped or not. *)
From stdpp Require Import gmap list.
From D Require Import tactics.
From D.Dot Require Import syn operational synLemmas typeExtractionSyn.

Set Primitive Projections.
Set Implicit Arguments.

Implicit Types
         (T: ty) (v: vl) (e: tm) (p: path) (d: dm) (ds: dms) (vs: vls)
         (Γ : ctx) (g: stys) (n: nat).

Record Traversal {travStateT: Type} :=
  {
    upS: travStateT → travStateT;
    varP: travStateT → nat → Prop;
    dtysynP: travStateT → ty → Prop;
    dtysemP: travStateT → vls → stamp → Prop;
  }.
Global Arguments Traversal _: clear implicits.

Definition is_unstamped_trav: Traversal unit :=
  {|
    upS := id;
    varP := λ s n, True;
    dtysynP := λ s T, True;
    dtysemP := λ s vs s, False;
  |}.

Definition is_stamped_trav: Traversal (nat * stys) :=
  {|
    upS := λ '(n, g), (S n, g);
    varP := λ '(n, g) i, i < n;
    dtysynP := λ ts T, False;
    dtysemP := λ '(n, g) vs s, ∃ T', g !! s = Some T' ∧ nclosed T' (length vs);
  |}.

Section fold.
  Context `(trav: Traversal travStateT).

  Inductive forall_traversal_vl: travStateT → vl → Prop :=
    | trav_var_vl ts i: trav.(varP) ts i → forall_traversal_vl ts (var_vl i)
    | trav_vabs ts t: forall_traversal_tm (trav.(upS) ts) t →
                          forall_traversal_vl ts (vabs t)
    | trav_vnat ts n: forall_traversal_vl ts (vnat n)
    | trav_vobj ts ds : Forall (forall_traversal_dm (trav.(upS) ts)) (map snd ds) →
                     forall_traversal_vl ts (vobj ds)
  with
  forall_traversal_tm: travStateT → tm → Prop :=
  | trav_tv ts v: forall_traversal_vl ts v → forall_traversal_tm ts (tv v)
  | trav_tapp ts t1 t2:
      forall_traversal_tm ts t1 →
      forall_traversal_tm ts t2 →
      forall_traversal_tm ts (tapp t1 t2)
  | trav_tproj ts t l:
      forall_traversal_tm ts t →
      forall_traversal_tm ts (tproj t l)
  | trav_tskip ts t:
      forall_traversal_tm ts t →
      forall_traversal_tm ts (tskip t)
  with
  forall_traversal_dm: travStateT → dm → Prop :=
  | trav_dvl ts v:
      forall_traversal_vl ts v →
      forall_traversal_dm ts (dvl v)
  | trav_dtysyn ts T:
      forall_traversal_ty ts T →
      trav.(dtysynP) ts T →
      forall_traversal_dm ts (dtysyn T)
  | trav_dtysem ts vs s:
      trav.(dtysemP) ts vs s →
      Forall (forall_traversal_vl ts) vs →
      forall_traversal_dm ts (dtysem vs s)
  with
  forall_traversal_path: travStateT → path → Prop :=
  | trav_pv ts v:
    forall_traversal_vl ts v →
    forall_traversal_path ts (pv v)
  | trav_pself ts p l:
    forall_traversal_path ts p →
    forall_traversal_path ts (pself p l)
  with
  forall_traversal_ty: travStateT → ty → Prop :=
  | trav_TTop ts: forall_traversal_ty ts TTop
  | trav_TBot ts: forall_traversal_ty ts TBot
  | trav_TAnd ts T1 T2:
      forall_traversal_ty ts T1 →
      forall_traversal_ty ts T2 →
      forall_traversal_ty ts (TAnd T1 T2)
  | trav_TOr ts T1 T2:
      forall_traversal_ty ts T1 →
      forall_traversal_ty ts T2 →
      forall_traversal_ty ts (TOr T1 T2)
  | trav_TLater ts T1:
      forall_traversal_ty ts T1 →
      forall_traversal_ty ts (TLater T1)
  | trav_TAll ts T1 T2:
      forall_traversal_ty ts T1 →
      forall_traversal_ty (trav.(upS) ts) T2 →
      forall_traversal_ty ts (TAll T1 T2)
  | trav_TMu ts T1:
      forall_traversal_ty (trav.(upS) ts) T1 →
      forall_traversal_ty ts (TMu T1)
  | trav_TVMem ts l T1:
      forall_traversal_ty ts T1 →
      forall_traversal_ty ts (TVMem l T1)
  | trav_TTMem ts l T1 T2:
      forall_traversal_ty ts T1 →
      forall_traversal_ty ts T2 →
      forall_traversal_ty ts (TTMem l T1 T2)
  | trav_TSel ts p l:
      forall_traversal_path ts p →
      forall_traversal_ty ts (TSel p l)
  | trav_TNat ts: forall_traversal_ty ts TNat
    .
End fold.

Notation is_unstamped_tm := (forall_traversal_tm is_unstamped_trav ()).
Notation is_unstamped_vl := (forall_traversal_vl is_unstamped_trav ()).
Notation is_unstamped_dm := (forall_traversal_dm is_unstamped_trav ()).
Notation is_unstamped_path := (forall_traversal_path is_unstamped_trav ()).
Notation is_unstamped_ty := (forall_traversal_ty is_unstamped_trav ()).

Notation is_stamped_tm n g := (forall_traversal_tm is_stamped_trav (n, g)).
Notation is_stamped_vl n g := (forall_traversal_vl is_stamped_trav (n, g)).
Notation is_stamped_dm n g := (forall_traversal_dm is_stamped_trav (n, g)).
Notation is_stamped_path n g := (forall_traversal_path is_stamped_trav (n, g)).
Notation is_stamped_ty n g := (forall_traversal_ty is_stamped_trav (n, g)).

Global Arguments upS /.
Global Arguments varP /.
Global Arguments dtysynP /.
Global Arguments dtysemP /.

Lemma is_stamped_idsσ_ren g m n j: j + n <= m → Forall (is_stamped_vl m g) (idsσ n).|[ren (+j)].
Proof.
  elim: n m j => [|n IHn] m j Ijm //=.
  repeat constructor => //=; first lia.
  asimpl; apply IHn; lia.
Qed.

Lemma is_stamped_idsσ g m n: n <= m → Forall (is_stamped_vl m g) (idsσ n).
Proof. pose proof (@is_stamped_idsσ_ren g m n 0) as H. asimpl in H. exact: H. Qed.

Hint Constructors forall_traversal_vl forall_traversal_tm forall_traversal_dm
     forall_traversal_path forall_traversal_ty.

Lemma not_stamped_dtysyn g n T:
  ¬ (is_stamped_dm n g (dtysyn T)).
Proof. by inversion 1. Qed.

Lemma is_stamped_dtysyn_mono g1 g2 n T:
  g1 ⊆ g2 →
  is_stamped_dm n g1 (dtysyn T) →
  is_stamped_dm n g2 (dtysyn T).
Proof. intros; exfalso. by eapply not_stamped_dtysyn. Qed.

Ltac with_is_stamped tac :=
  match goal with
    | H: is_stamped_ty _ _ _ |- _ => tac H
    | H: is_stamped_tm _ _ _ |- _ => tac H
    | H: is_stamped_vl _ _ _ |- _ => tac H
    | H: is_stamped_dm _ _ _ |- _ => tac H
    | H: is_stamped_path _ _ _ |- _ => tac H
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
  (∀ d__s g1 g2 n,
      g1 ⊆ g2 →
      is_stamped_dm n g1 d__s →
      is_stamped_dm n g2 d__s) ∧
  (∀ p__s g1 g2 n,
      g1 ⊆ g2 →
      is_stamped_path n g1 p__s →
      is_stamped_path n g2 p__s) ∧
  (∀ T__s g1 g2 n,
      g1 ⊆ g2 →
      is_stamped_ty n g1 T__s →
      is_stamped_ty n g2 T__s).
Proof.
  apply syntax_mut_ind;
    try by [ intros; with_is_stamped inverse; constructor; cbn in *; eauto].
  - move => ds Hds g1 g2 n Hg12 Hsg1. constructor.
    inversion_clear Hsg1; move: H => Hsg1.
    elim: ds Hds Hsg1 => [| d ds IHds] /= Hds Hdsg1; constructor;
    inverse Hdsg1; inverse Hds; eauto.
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
Lemma is_stamped_mono_dm g1 g2 n d__s:
  g1 ⊆ g2 →
  is_stamped_dm n g1 d__s →
  is_stamped_dm n g2 d__s.
Proof. unmut_lemma is_stamped_mono_mut. Qed.
Lemma is_stamped_mono_path g1 g2 n p__s:
  g1 ⊆ g2 →
  is_stamped_path n g1 p__s →
  is_stamped_path n g2 p__s.
Proof. unmut_lemma is_stamped_mono_mut. Qed.
Lemma is_stamped_mono_ty g1 g2 n T__s:
  g1 ⊆ g2 →
  is_stamped_ty n g1 T__s →
  is_stamped_ty n g2 T__s.
Proof. unmut_lemma is_stamped_mono_mut. Qed.

(* XXX Still used? *)
Lemma is_stamped_dtysem_mono g1 g2 n s vs:
  g1 ⊆ g2 →
  is_stamped_dm n g1 (dtysem vs s) →
  is_stamped_dm n g2 (dtysem vs s).
Proof. apply is_stamped_mono_dm. Qed.

Lemma swap_snd_list_pair_rename r ds: map snd (list_pair_rename r ds) = map (rename r) (map snd ds).
Proof.
  rewrite /list_pair_rename /mapsnd !map_map /=.
  elim: ds => [| [a b] ds IHds] //=; by f_equal.
Qed.

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

From D.Dot Require Import closed_subst.

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
  (∀ d g r i j,
    is_stamped_ren i j g r →
    is_stamped_dm i g d →
    is_stamped_dm j g (rename r d)) ∧
  (∀ p g r i j,
    is_stamped_ren i j g r →
    is_stamped_path i g p →
    is_stamped_path j g (rename r p)) ∧
  (∀ T g r i j,
    is_stamped_ren i j g r →
    is_stamped_ty i g T →
    is_stamped_ty j g (rename r T)).
Proof.
  apply syntax_mut_ind; intros; with_is_stamped ltac:(fun H => inversion_clear H);
    cbn in *; try by [constructor; cbn; eauto].
  - eauto.
  - constructor; rewrite swap_snd_list_pair_rename Forall_fmap;
      by decompose_Forall; eauto.
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

Lemma is_stamped_nclosed_ty T g i:
  is_stamped_ty i g T →
  nclosed T i.
Admitted.

Lemma is_stamped_sub_vl v g s m n:
  is_stamped_sub n m g s →
  is_stamped_vl n g v →
  is_stamped_vl m g v.[s]
with
is_stamped_sub_ty T g s m n:
  is_stamped_sub n m g s →
  is_stamped_ty n g T →
  is_stamped_ty m g T.|[s].
Proof.
  -
    move: s m n. induction v => s i j Hss HsV //=;
    with_is_stamped ltac:(fun H => inversion_clear H); try econstructor;
      eauto 3 using is_stamped_sub_up with lia.
      all: cbn in *.
      admit.
      (* Check swap_snd_list_pair_rename.
      Print list_pair_hsubst. *)
      (* rewrite swap_snd_list_pair_rename. *)
      rewrite Forall_fmap.
      admit.
  - move: s m n; induction T => s m n Hss HsT //;
    with_is_stamped ltac:(fun H => inversion_clear H); constructor; cbn;
      eauto 3 using is_stamped_sub_up.
    (* Missing: case for paths. *)
Admitted.

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

Lemma is_stamped_sub_rev_vl g v s i j:
  nclosed_vl v i →
  is_stamped_vl j g (v.[s]) →
  is_stamped_vl i g v.
Admitted.

Lemma is_stamped_sub_rev_ty g T s i j:
  nclosed T i →
  is_stamped_ty j g (T.|[s]) →
  is_stamped_ty i g T.
Admitted.

Lemma is_stamped_sub_one_rev i T v g:
  nclosed T (S i) →
  is_stamped_ty i g (T.|[v/]) →
  is_stamped_ty (S i) g T.
Admitted.

Lemma is_stamped_ren_ty i T g:
  nclosed T i →
  is_stamped_ty i g T <->
  is_stamped_ty (S i) g (T.|[ren (+1)]).
Proof.
  have Hs: is_stamped_sub i (S i) g (ren (+1)). by apply is_stamped_ren_shift; lia.
  split; intros; by [ eapply is_stamped_sub_ty | eapply is_stamped_sub_rev_ty].
Qed.
