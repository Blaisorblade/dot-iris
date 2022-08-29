From D Require Export iris_prelude saved_interp_n proper proofmode_pupd.
From D Require Import persistence.
From D.DSub Require Import syn.
From D.DSub Require Import ty_interp_subst_lemmas.
Export syn.

Include SavedHoInterp VlSorts. (* Defines [envD] and needed by TyInterpLemmas. *)
Include TyInterpLemmas VlSorts.
Export ty_interp_lemmas.

Set Suggest Proof Using.
Set Default Proof Using "Type*".

(** Deduce types from variable names, like on paper, for readability and to help
    type inference for some overloaded operations (e.g. substitution). *)
Implicit Types
         (L T U : ty) (v w : vl) (e : tm)
         (Γ : ctx) (vs : vls) (ρ : var → vl).

(** The logical relation core is the [interp], interprets *open* types into
    predicates over *closed* values. Hence, [interp T ρ v] uses its argument [ρ]
    to interpret anything contained in T, but not things contained in v.

    Semantic judgements must apply instead to open terms/value/paths; therefore,
    they are defined using closing substitution on arguments of [interp].

    Additionally, both apply to *unstamped* syntax, hence they only expect
    [vty] and not [vstamp] for type member definitions.
 *)

(* The only point of these instances is to select Σ uniquely. *)
Class dsubSynG (Σ : gFunctors) := DsubSynG {
   dsubSynG_persistent :> CmraPersistent (iResUR Σ);
}.

From D.DSub Require Export rules.
#[global] Instance dsubsynG_irisG `{!dsubSynG Σ} : irisGS dlang_lang Σ := {
  irisG_langdet := _;
}.

(* Use Program without its extended pattern-matching compiler; we only need
   its handling of coercions. *)
Unset Program Cases.

Section vl_has_semtype.
  Context `{!dsubSynG Σ}.

  Notation D := (vl -d> iPropO Σ).

  Definition vl_has_semtype : vl -d> D -d> (ty -d> envD Σ) -d> iPropO Σ :=
    λI v φ rinterp,
    ∃ T, ⌜ v = vty T ⌝ ∧ ∀ w, ▷ (φ w ≡ rinterp T ids w).
  #[global] Arguments vl_has_semtype /.

  #[global] Instance vl_has_semtype_contractive n v :
    Proper (dist_later n ==> dist_later n ==> dist n) (vl_has_semtype v).
  Proof. solve_contractive_ho. Qed.
End vl_has_semtype.

Notation "v ↗[ rinterp ] φ" := (vl_has_semtype v φ rinterp) (at level 20).

Section logrel.
  Context `{!dsubSynG Σ}.

  Notation D := (vl -d> iPropO Σ).
  Implicit Types (interp : envD Σ) (φ : D).

  Definition interp_expr : envD Σ -> (var → vl) -d> tm -d> iPropO Σ :=
    λ interp, λI ρ t, WP t {{ interp ρ }}.
  #[global] Arguments interp_expr /.

  Definition interp_nat : envD Σ := λI ρ v, ∃ n, ⌜v = vint n⌝.
  #[global] Arguments interp_nat /.

  Definition interp_top : envD Σ := λI ρ v, True.
  #[global] Arguments interp_top /.

  Definition interp_bot : envD Σ := λI ρ v, False.
  #[global] Arguments interp_bot /.

  Definition interp_later : envD Σ -> envD Σ :=
    λI interp ρ v, ▷ interp ρ v.
  #[global] Arguments interp_later /.
  #[local] Instance interp_later_contractive : Contractive interp_later.
  Proof. solve_contractive_ho. Qed.

  (* Function types; this definition is contractive (similarly to what's
     useful for equi-recursive types). *)
  Definition interp_forall : envD Σ -> envD Σ -> envD Σ :=
    λI interp1 interp2 ρ v,
    ∃ t, ⌜ v = vabs t ⌝ ∧
      □ ▷ ∀ w, interp1 ρ w → interp_expr interp2 (w .: ρ) t.|[w/].
  #[global] Arguments interp_forall /.
  #[local] Instance interp_forall_contractive n :
    Proper (dist_later n ==> dist_later n ==> dist n) interp_forall.
  Proof. solve_contractive_ho. Qed.

  Lemma vl_has_semtype_agree rinterp v (φ1 φ2 : D) :
    v ↗[ rinterp ] φ1 -∗
    v ↗[ rinterp ] φ2 -∗
    ∀ w, ▷ (φ1 w ≡ φ2 w).
  Proof.
    iIntros "/= #H1 #H2" (w).
    iDestruct "H1" as (T1 ?) "#Heq1"; iDestruct "H2" as (T ?) "#Heq2"; simplify_eq.
    iNext.
    by iRewrite ("Heq1" $! w); iRewrite ("Heq2" $! w).
  Qed.
  #[local] Hint Opaque vl_has_semtype : typeclass_instances.
  #[local] Opaque vl_has_semtype.

  Definition interp_tmem :
    (ty -d> envD Σ) -> envD Σ -> envD Σ -> envD Σ :=
    λI rinterp interpL interpU ρ v,
    ∃ φ, v ↗[ rinterp ] φ ∧
       □ ((∀ v, interpL ρ v → □ ▷ φ v) ∧
          (∀ v, □ ▷ φ v → interpU ρ v)).
  #[global] Arguments interp_tmem /.
  #[local] Instance interp_tmem_contractive n :
    Proper (dist_later n ==> dist n ==> dist n ==> dist n) interp_tmem.
  Proof. solve_contractive_ho. Qed.

  Definition interp_sel : (ty -d> envD Σ) -d> vl -d> envD Σ :=
    λI rinterp w ρ v,
    ∃ ϕ, w.[ρ] ↗[rinterp] ϕ ∧ □ ▷ ϕ v.
  #[global] Arguments interp_sel /.
  #[local] Instance interp_sel_contractive n :
    Proper (dist_later n ==> eq ==> dist n) interp_sel.
  Proof. solve_contractive_ho. Qed.

  (* This is a structurally recursive Coq function: we use [rec rinterp] for
     structurally recursive calls, and [rinterp] for guarded recursive calls, only legal under [▷].

     For calls that are structurally recursive and are under [▷], we prefer
     [rinterp] to [rec rinterp], to simplify proofs of the unfolding lemmas.
   *)
  Definition interp_rec : (ty -d> envD Σ) → ty -d> envD Σ :=
    fix rec rinterp T :=
    match T with
    | TLater T => interp_later (rinterp T)
    | TTMem L U => interp_tmem rinterp (rec rinterp L) (rec rinterp U)
    | TInt => interp_nat
    | TAll T1 T2 => interp_forall (rinterp T1) (rinterp T2)
    | TSel w => interp_sel rinterp w
    | TTop => interp_top
    | TBot => interp_bot
    end.

  (* solve_contractive is really not happy about checking this code. *)
  #[global] Instance interp_rec_contractive : Contractive interp_rec.
  Proof.
    move => n i1 i2 Heq T /=; induction T.
    all: cbn -[interp_later interp_forall interp_tmem interp_sel interp_nat interp_top interp_bot].
    all: try by [f_contractive | f_equiv| ].
  Qed.

  #[global] Instance dsub_interp : TyInterp ty Σ := fixpoint interp_rec.

  Lemma fixpoint_interp_eq1 T : ⟦ T ⟧ ≡ interp_rec ty_interp T.
  Proof. apply: (fixpoint_unfold interp_rec). Qed.

  Lemma fixpoint_interp_rec_eq :
    ty_interp ≡@{ty -d> envD Σ} interp_rec ty_interp.
  Proof. apply: (fixpoint_unfold interp_rec). Qed.

  (* Unused. *)
  Lemma fixpoint_interp_eq2 T ρ : ⟦ T ⟧ ρ ≡ interp_rec ty_interp T ρ.
  Proof. apply: (fixpoint_unfold interp_rec). Qed.
  Lemma fixpoint_interp_eq3 T ρ v : ⟦ T ⟧ ρ v ≡ interp_rec ty_interp T ρ v.
  Proof. apply: (fixpoint_unfold interp_rec). Qed.

  Lemma interp_TInt ρ v : ⟦ TInt ⟧ ρ v ≡ interp_nat ρ v.
  Proof. apply: (fixpoint_unfold interp_rec). Qed.
  Lemma interp_TSel ρ v w : ⟦ TSel w ⟧ ρ v ≡ interp_sel ty_interp w ρ v.
  Proof. apply: (fixpoint_unfold interp_rec). Qed.
  Lemma interp_TTop ρ v : ⟦ TTop ⟧ ρ v ≡ interp_top ρ v.
  Proof. apply: (fixpoint_unfold interp_rec). Qed.
  Lemma interp_TBot ρ v : ⟦ TBot ⟧ ρ v ≡ interp_bot ρ v.
  Proof. apply: (fixpoint_unfold interp_rec). Qed.
  Lemma interp_TAll T1 T2 ρ v : ⟦ TAll T1 T2 ⟧ ρ v ≡ interp_forall ⟦ T1 ⟧ ⟦ T2 ⟧ ρ v.
  Proof. apply: (fixpoint_unfold interp_rec). Qed.
  Lemma interp_TLater T1 ρ v : ⟦ TLater T1 ⟧ ρ v ≡ interp_later ⟦ T1 ⟧ ρ v.
  Proof. apply: (fixpoint_unfold interp_rec). Qed.

  Ltac rewrite_interp := repeat (rewrite fixpoint_interp_eq1 //=; repeat f_equiv).

  Lemma interp_TTMem T1 T2 ρ v : ⟦ TTMem T1 T2 ⟧ ρ v ≡ interp_tmem ty_interp ⟦ T1 ⟧ ⟦ T2 ⟧ ρ v.
  Proof. rewrite_interp. Qed.
End logrel.

Notation "⟦ T ⟧ₑ" := (interp_expr ⟦ T ⟧).

(** Unfold uses of interp, but only if the argument allows progress. *)
Ltac unfold_interp :=
  rewrite /=
    ?(interp_TLater, interp_TAll, interp_TInt, interp_TTMem,
    interp_TSel, interp_TTop, interp_TBot) /=.

Hint Rewrite @interp_TLater @interp_TAll @interp_TInt @interp_TTMem
    @interp_TSel @interp_TTop @interp_TBot : ds_interp.
Ltac unfold_interp_autorw := simpl; autorewrite with ds_interp; simpl.

Ltac setoid_unfold_interp :=
  try setoid_rewrite interp_TAll;
  try setoid_rewrite interp_TLater;
  try setoid_rewrite interp_TSel;
  try setoid_rewrite interp_TInt;
  try setoid_rewrite interp_TTMem;
  try setoid_rewrite interp_TTop;
  try setoid_rewrite interp_TBot;
  cbn.
#[global] Arguments ty_interp {_ _ _} _ : simpl never.

Section logrel_part2.
  Context `{!dsubSynG Σ}.

  #[global] Instance interp_lemmas : TyInterpLemmas ty Σ.
  Proof.
    split; induction T => sb1 sb2 w; unfold_interp;
      properness; rewrite /= ?scons_up_swap ?subst_comp; trivial.
  Qed.

  #[global] Instance interp_persistent T ρ v :
    Persistent (⟦ T ⟧ ρ v).
  Proof. move: v ρ; induction T => w ρ; unfold_interp; try apply _. Qed.

  (* XXX here we needn't add a variable to the scope of its own type. But that won't hurt. *)
  Fixpoint interp_env (Γ : ctx) (ρ : var → vl) : iProp Σ :=
    match Γ with
    | T :: Γ' => interp_env Γ' (stail ρ) ∧ ⟦ T ⟧ ρ (shead ρ)
    | nil => True
    end.

  Notation "G⟦ Γ ⟧" := (interp_env Γ).

  #[global] Instance interp_env_persistent Γ ρ :
    Persistent (G⟦ Γ ⟧ ρ).
  Proof. elim: Γ ρ => [|τ Γ IHΓ] ρ /=; apply _. Qed.

  Definition ietp Γ T e : iProp Σ :=
    □ ∀ ρ, G⟦Γ⟧ ρ → ⟦T⟧ₑ ρ (e.|[ρ]).
  #[global] Arguments ietp /.
  Notation "Γ ⊨ e : T" := (ietp Γ T e) (at level 74, e, T at next level).

  Definition ietpi Γ T e i : iProp Σ :=
    □ ∀ ρ, G⟦Γ⟧ ρ → ▷^i ⟦T⟧ₑ ρ (e.|[ρ]).
  #[global] Arguments ietpi /.
  Notation "Γ ⊨ e : T , i" := (ietpi Γ T e i) (at level 74, e, T at next level).

  (** Indexed Subtyping. Defined on closed values. We must require closedness
      explicitly, since closedness now does not follow from being well-typed later. *)
  Definition istpi Γ T1 T2 i j : iProp Σ :=
    □ ∀ ρ v, G⟦Γ⟧ ρ → (▷^i ⟦T1⟧ ρ v) → ▷^j ⟦T2⟧ ρ v.
  #[global] Arguments istpi /.

  Definition delayed_ivstp Γ T1 T2 i : iProp Σ :=
    □ ∀ ρ, G⟦Γ⟧ρ → ▷^i ∀v, ⟦T1⟧ ρ v → ⟦T2⟧ ρ v.
  #[global] Arguments delayed_ivstp /.

  #[global] Instance ietp_persistent Γ T e : Persistent (ietp Γ T e) := _.
  #[global] Instance ietpi_persistent Γ T e i : Persistent (ietpi Γ T e i) := _.
  #[global] Instance istpi_persistent Γ T1 T2 i j : Persistent (istpi Γ T1 T2 i j) := _.
End logrel_part2.

Notation "G⟦ Γ ⟧" := (interp_env Γ).

(** Expression typing *)
Notation "Γ ⊨ e : T" := (ietp Γ T e) (at level 74, e, T at next level).
(** Indexed expression typing *)
Notation "Γ ⊨ e : T , i" := (ietpi Γ T e i) (at level 74, e, T at next level).

Notation "Γ ⊨ T1 , i <: T2 , j" := (istpi Γ T1 T2 i j) (at level 74, T1, T2, i, j at next level).
Notation "Γ ⊨[ i  ] T1 <: T2" := (delayed_ivstp Γ T1 T2 i) (at level 74, T1, T2 at next level).

Section logrel_lemmas.
  Context `{!dsubSynG Σ}.

  Lemma iterate_TLater_later i T ρ v :
    ⟦ iterate TLater i T ⟧ ρ v ⊣⊢ ▷^i ⟦ T ⟧ ρ v.
  Proof.
    elim: i => [|i IHi] //.
    rewrite iterate_S /=; unfold_interp; rewrite IHi //.
  Qed.

  Lemma semantic_typing_uniform_step_index Γ T e i :
    Γ ⊨ e : T -∗ Γ ⊨ e : T, i.
  Proof.
    pupd. iIntros "#H !> %ρ #HΓ".
    iInduction i as [|i] "IHi". by iApply "H". iExact "IHi".
  Qed.

  Lemma interp_env_lookup Γ ρ T x :
    Γ !! x = Some T →
    G⟦ Γ ⟧ ρ -∗ ⟦ shiftN x T ⟧ ρ (ρ x).
  Proof.
    elim: Γ ρ x => [//|τ' Γ' IHΓ] ρ x Hx /=.
    iDestruct 1 as "[Hg Hv]". move: x Hx => [ [->] | x Hx] /=.
    - rewrite hsubst_id. by [].
    - rewrite hrenS.
      iApply (interp_weaken_one (shiftN x T)).
      iApply (IHΓ ((+1) >>> ρ) x Hx with "Hg").
  Qed.

  Context {Γ}.
  Lemma Sub_Refl T i : ⊢ Γ ⊨ T, i <: T, i.
  Proof. pupd. by iIntros "!> /= **". Qed.

  Lemma Sub_Trans T1 T2 T3 i1 i2 i3 :
    Γ ⊨ T1, i1 <: T2, i2 -∗ Γ ⊨ T2, i2 <: T3, i3 -∗ Γ ⊨ T1, i1 <: T3, i3.
  Proof.
    pupd; iIntros "#Hsub1 #Hsub2 !> /= * #Hg #HT".
    iApply ("Hsub2" with "Hg (Hsub1 Hg [//])").
  Qed.

  Lemma DSub_Refl T i : ⊢ Γ ⊨[i] T <: T.
  Proof. pupd; by iIntros "/= !> ** !> **". Qed.

  Lemma DSub_Trans T1 T2 T3 i :
    Γ ⊨[i] T1 <: T2 -∗ Γ ⊨[i] T2 <: T3 -∗ Γ ⊨[i] T1 <: T3.
  Proof.
    pupd; iIntros "#Hsub1 #Hsub2 !> /= * #Hg".
    iSpecialize ("Hsub1" with "Hg"); iSpecialize ("Hsub2" with "Hg").
    iIntros "!>" (v) "#HT". iApply "Hsub2". by iApply "Hsub1".
  Qed.
End logrel_lemmas.
