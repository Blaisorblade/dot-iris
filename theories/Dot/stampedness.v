(** Define purely syntactically whether a term is stamped or not. *)
From stdpp Require Import gmap.
From D Require Import tactics.
From D.Dot Require Import dotsyn operational typeExtractionSyn.

Set Primitive Projections.
Set Implicit Arguments.

Implicit Types
         (T: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (vs: vls)
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
    varP := λ ts n, True;
    dtysynP := λ ts T, False;
    dtysemP := λ '(n, g) vs s, ∃ T', g !! s = Some T' ∧ nclosed T' (length vs) ∧ nclosed_σ vs n;
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
      (* This is weird, but apparently we get away without checking that
         these values are syntactic. *)
      (* Forall (forall_traversal_vl ts) vs → *)
      forall_traversal_dm ts (dtysem vs s)
  with
  forall_traversal_path: travStateT → path → Prop :=
  | trav_pv ts v:
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

Lemma stamped_idsσ_ren g m n r: Forall (is_stamped_vl m g) (idsσ n).|[ren r].
Proof.
  elim: n m r => [|n IHn] m r //=.
  repeat constructor => //=. asimpl. apply IHn.
Qed.

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

Lemma is_stamped_dtysem_mono g1 g2 n s vs:
  g1 ⊆ g2 →
  is_stamped_dm n g1 (dtysem vs s) →
  is_stamped_dm n g2 (dtysem vs s).
Proof.
  inversion 2; subst; simpl in *; ev.
  repeat econstructor => //=. by eapply map_subseteq_spec.
Qed.

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
  apply syntax_mut_ind.
  all: try by [ intros; with_is_stamped inverse; by [ eapply is_stamped_dtysem_mono | constructor; cbn in *; eauto]].
  move => ds Hds g1 g2 n Hg12 Hsg1. constructor.
  inversion_clear Hsg1; move: H => Hsg1.
  elim: ds Hds Hsg1 => [| d ds IHds] /= Hds Hdsg1; constructor;
  inverse Hdsg1; inverse Hds; eauto.
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
