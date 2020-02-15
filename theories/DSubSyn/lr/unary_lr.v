From iris.proofmode Require Import tactics.
From D Require Export iris_prelude.
From D Require Import ty_interp_subst_lemmas.
From D.DSub Require Export dlang_inst.

Include TyInterpLemmas VlSorts dlang_inst.
Export ty_interp_lemmas.

Set Suggest Proof Using.
Set Default Proof Using "Type*".

(** Deduce types from variable names, like on paper, for readability and to help
    type inference for some overloaded operations (e.g. substitution). *)
Implicit Types
         (L T U : ty) (v : vl) (e : tm)
         (Γ : ctx) (vs : vls) (ρ : var → vl).

(** The logical relation core is the [interp], interprets *open* types into
    predicates over *closed* values. Hence, [interp T ρ v] uses its argument [ρ]
    to interpret anything contained in T, but not things contained in v.

    Semantic judgements must apply instead to open terms/value/paths; therefore,
    they are defined using closing substitution on arguments of [interp].

    Similar comments apply to [def_interp].

    Additionally, both apply to *translated* arguments, hence they only expect
    [dtysem] and not [dtysyn] for type member definitions.
 *)

(* The only point of these instances is to select Σ uniquely. *)
Class dsubSynG (Σ: gFunctors) := DsubSynG {}.

Instance dsubsynG_irisG `{!dsubSynG Σ}: irisG dlang_lang Σ := {
  state_interp σ κs _ := True%I;
  fork_post _ := True%I;
}.

(* Use Program without its extended pattern-matching compiler; we only need
   its handling of coercions. *)
Unset Program Cases.

Section logrel.
  Context `{!dsubSynG Σ}.

  Notation D := (vl -d> iPropO Σ).
  Implicit Types (interp : envD Σ) (φ : D).

  Program Definition interp_expr : envD Σ -n> (var → vl) -d> tm -d> iPropO Σ :=
    λne interp, λ ρ t, WP t {{ interp ρ }} %I.
  Solve All Obligations with solve_proper_ho.
  Global Arguments interp_expr /.

  Definition interp_nat : envD Σ := λ ρ v, (∃ n, ⌜v = vnat n⌝) %I.
  Global Arguments interp_nat /.

  Definition interp_top : envD Σ := λ ρ v, True%I.
  Global Arguments interp_top /.

  Definition interp_bot : envD Σ := λ ρ v, False%I.
  Global Arguments interp_bot /.

  Program Definition interp_later: envD Σ -n> envD Σ :=
    λne interp, λ ρ v, (▷ interp ρ v)%I.
  Solve All Obligations with solve_proper_ho.
  Global Arguments interp_later /.

  (* Paolo: This definition is contractive (similarly to what's useful for
     equi-recursive types).
     However, I am not sure we need this; it'd be good to
     write an example where this makes a difference.
     I think that would be something like
     nu x. { T = TNat; U = x.T -> x.T }:
     mu (x: {T <: TNat; U <: x.T -> TNat}).
     If the function type constructor is not contractive but only non-expansive,
     typechecking this example needs to establish x.T <: TNat having in context
     only x: {T <: TNat; U <: x.T -> TNat}.
    *)

  Program Definition interp_forall: envD Σ -n> envD Σ -n> envD Σ :=
    λne interp1 interp2, λ ρ v,
    (∃ t, ⌜ v = vabs t ⌝ ∧
      □ ▷ ∀ w, interp1 ρ w → interp_expr interp2 (w .: ρ) t.|[w/])%I.
  Solve All Obligations with solve_proper_ho.
  Global Arguments interp_forall /.

  Program Definition vl_has_semtype : (ty -d> envD Σ) -n> vl -d> D -n> iPropO Σ :=
    λne rinterp, λ v, λne φ,
    (∃ T, ⌜ v = vty T ⌝ ∧ ∀ w, (φ w ≡ rinterp T ids w))%I.
  Solve All Obligations with solve_proper_ho.
  Global Arguments vl_has_semtype /.
  Notation "[ rinterp ] v ↗ φ" := (vl_has_semtype rinterp v φ) (at level 20).

  Lemma vl_has_semtype_agree rinterp v (φ1 φ2 : D):
    (▷ [ rinterp ] v ↗ φ1 →
     ▷ [ rinterp ] v ↗ φ2 →
     ∀ w, ▷ (φ1 w ≡ φ2 w))%I.
  Proof.
    iIntros "/= #H1 #H2" (w).
    iDestruct "H1" as (T1) "[>% #Heq1]". iDestruct "H2" as (T) "[>% #Heq2]"; simplify_eq.
    iNext.
    by iRewrite ("Heq1" $! w); iRewrite ("Heq2" $! w).
  Qed.

  Program Definition interp_tmem :
    (ty -d> envD Σ) -n> envD Σ -n> envD Σ -n> envD Σ :=
    λne rinterp interpL interpU, λ ρ v,
    (∃ φ, ▷ [ rinterp ] v ↗ φ ∧
       □ ((∀ v, ▷ interpL ρ v → ▷ □ φ v) ∧
          (∀ v, ▷ □ φ v → ▷ interpU ρ v)))%I.
  Solve All Obligations with solve_proper_ho.
  Global Arguments interp_tmem /.

  Global Instance interp_tmem_contractive : Contractive interp_tmem.
  Proof. solve_contractive_ho. Qed.

  Program Definition interp_sel: (ty -d> envD Σ) -n> vl -d> envD Σ :=
    λne rinterp, λ w ρ v,
    (▷ ∃ ϕ, [rinterp] w.[ρ] ↗ ϕ ∧ □ ϕ v)%I.
  Solve All Obligations with solve_proper_ho.
  Global Arguments interp_sel /.
  Global Instance interp_sel_contractive : Contractive interp_sel.
  Proof. solve_contractive_ho. Qed.

  (* This is a structurally recursive Coq function.
     Non-structurally recursive calls must happen under [▷] and use [rinterp]. *)
  Definition interp_rec: (ty -d> envD Σ) -> ty -d> envD Σ :=
    fix rec rinterp T :=
    match T with
    | TLater T => interp_later (rec rinterp T)
    | TTMem L U => interp_tmem rinterp (rec rinterp L) (rec rinterp U)
    | TNat => interp_nat
    | TAll T1 T2 => interp_forall (rec rinterp T1) (rec rinterp T2)
    | TSel w => interp_sel rinterp w
    | TTop => interp_top
    | TBot => interp_bot
    end%I.

  (* solve_contractive is really not happy about checking this code. *)
  Global Instance interp_rec_contractive : Contractive interp_rec.
  Proof.
    move => n i1 i2 Heq T /=; induction T.
    (* Generic but slow *)
    (* all: time (cbn -[interp_forall interp_tmem interp_sel interp_nat] in *; trivial;
      repeat (match goal with
                H : _ ≡{_}≡ _|- _ => apply dist_S, H || apply H
              end || (f_contractive; cbn -[interp_forall interp_tmem interp_sel interp_nat] in * ) || f_equiv)). *)
    all: cbn -[interp_later interp_forall interp_tmem interp_sel interp_nat];
      try by [apply interp_sel_contractive|];
      rewrite ?IHT ?IHT2; f_equiv; rewrite IHT1 //.
    exact: interp_tmem_contractive.
  Qed.

  Program Lemma fixpoint_interp_rec_eq:
    fixpoint interp_rec ≡ interp_rec (fixpoint interp_rec).
  Proof. exact: (fixpoint_unfold interp_rec). Qed.

  Global Instance interp : TyInterp ty Σ := fixpoint interp_rec.

  Lemma fixpoint_interp_eq1 T: interp T ≡ interp_rec interp T.
  Proof. apply fixpoint_interp_rec_eq. Qed.
  Lemma fixpoint_interp_eq2 T ρ: interp T ρ ≡ interp_rec interp T ρ.
  Proof. apply fixpoint_interp_rec_eq. Qed.
  Lemma fixpoint_interp_eq3 T ρ v: interp T ρ v ≡ interp_rec interp T ρ v.
  Proof. apply fixpoint_interp_rec_eq. Qed.

  Ltac rewrite_interp := rewrite /ty_interp; repeat first [rewrite fixpoint_interp_eq3 | progress (repeat f_equiv; rewrite ?fixpoint_interp_eq1 //=) | move => ? /= ].
  Lemma interp_TAll T1 T2 ρ v: interp (TAll T1 T2) ρ v ≡ interp_forall ⟦ T1 ⟧ ⟦ T2 ⟧ ρ v.
  Proof. rewrite_interp. Qed.
  Lemma interp_TNat ρ v: interp TNat ρ v ≡ interp_nat ρ v.
  Proof. rewrite_interp. Qed.
  Lemma interp_TLater T1 ρ v: interp (TLater T1) ρ v ≡ interp_later ⟦ T1 ⟧ ρ v.
  Proof. rewrite_interp. Qed.
  Lemma interp_TTMem T1 T2 ρ v: interp (TTMem T1 T2) ρ v ≡ interp_tmem ty_interp ⟦ T1 ⟧ ⟦ T2 ⟧ ρ v.
  Proof. rewrite_interp. Qed.
  Lemma interp_TSel ρ v w: interp (TSel w) ρ v ≡ interp_sel ty_interp w ρ v.
  Proof. rewrite_interp. Qed.
  Lemma interp_TTop ρ v: interp TTop ρ v ≡ interp_top ρ v.
  Proof. rewrite_interp. Qed.
  Lemma interp_TBot ρ v: interp TBot ρ v ≡ interp_bot ρ v.
  Proof. rewrite_interp. Qed.
End logrel.

Notation "⟦ T ⟧ₑ" := (interp_expr ⟦ T ⟧).

(** Unfold uses of interp, but only if the argument allows progress. *)
Ltac unfold_interp :=
  rewrite /=
    ?interp_TLater ?interp_TAll ?interp_TNat ?interp_TTMem
    ?interp_TSel ?interp_TTop ?interp_TBot /=.

Ltac setoid_unfold_interp :=
  try setoid_rewrite interp_TAll;
  try setoid_rewrite interp_TLater;
  try setoid_rewrite interp_TSel;
  try setoid_rewrite interp_TNat;
  try setoid_rewrite interp_TTMem;
  try setoid_rewrite interp_TTop;
  try setoid_rewrite interp_TBot;
  cbn.

Section logrel_part2.
  Context `{!dsubSynG Σ}.

  Global Instance interp_lemmas: TyInterpLemmas ty Σ.
  Proof.
    split; induction T => sb1 sb2 w; unfold_interp;
      properness; rewrite /= ?scons_up_swap; trivial.
    autosubst.
  Qed.

  Global Instance interp_persistent T ρ v :
    Persistent (⟦ T ⟧ ρ v).
  Proof. revert v ρ; induction T => w ρ; unfold_interp; try apply _. Qed.

  (* XXX here we needn't add a variable to the scope of its own type. But that won't hurt. *)
  Fixpoint interp_env (Γ : ctx) (ρ : var → vl) : iProp Σ :=
    match Γ with
    | T :: Γ' => interp_env Γ' (stail ρ) ∧ ⟦ T ⟧ ρ (shead ρ)
    | nil => True
    end%I.

  Notation "G⟦ Γ ⟧" := (interp_env Γ).

  Global Instance interp_env_persistent Γ ρ :
    Persistent (G⟦ Γ ⟧ ρ).
  Proof. elim: Γ ρ => [|τ Γ IHΓ] ρ /=; apply _. Qed.

  Definition ietp Γ T e : iProp Σ :=
    (□∀ ρ, G⟦Γ⟧ ρ → ⟦T⟧ₑ ρ (e.|[ρ]))%I.
  Global Arguments ietp /.
  Notation "Γ ⊨ e : T" := (ietp Γ T e) (at level 74, e, T at next level).

  Definition ietpi Γ T e i: iProp Σ :=
    (□∀ ρ, G⟦Γ⟧ ρ → ▷^i ⟦T⟧ₑ ρ (e.|[ρ]))%I.
  Global Arguments ietpi /.
  Notation "Γ ⊨ e : T , i" := (ietpi Γ T e i) (at level 74, e, T at next level).

  (** Indexed Subtyping. Defined on closed values. We must require closedness
      explicitly, since closedness now does not follow from being well-typed later. *)
  Definition istpi Γ T1 T2 i j: iProp Σ :=
    (□∀ ρ v, G⟦Γ⟧ ρ → (▷^i ⟦T1⟧ ρ v) → ▷^j ⟦T2⟧ ρ v)%I.
  Global Arguments istpi /.

  Definition delayed_ivstp Γ T1 T2 i: iProp Σ :=
    (□ ∀ ρ, G⟦Γ⟧ρ → ▷^i ∀v, ⟦T1⟧ ρ v → ⟦T2⟧ ρ v)%I.
  Global Arguments delayed_ivstp /.

  Global Instance ietp_persistent Γ T e : Persistent (ietp Γ T e) := _.
  Global Instance ietpi_persistent Γ T e i : Persistent (ietpi Γ T e i) := _.
  Global Instance istpi_persistent Γ T1 T2 i j : Persistent (istpi Γ T1 T2 i j) := _.
End logrel_part2.

Notation "G⟦ Γ ⟧" := (interp_env Γ).

(** Expression typing *)
Notation "Γ ⊨ e : T" := (ietp Γ T e) (at level 74, e, T at next level).
(** Indexed expression typing *)
Notation "Γ ⊨ e : T , i" := (ietpi Γ T e i) (at level 74, e, T at next level).

Notation "Γ ⊨ T1 , i <: T2 , j " := (istpi Γ T1 T2 i j) (at level 74, T1, T2, i, j at next level).
Notation "Γ ⊨[ i  ] T1 <: T2" := (delayed_ivstp Γ T1 T2 i) (at level 74, T1, T2 at next level).

Section logrel_lemmas.
  Context `{!dsubSynG Σ}.

  Lemma iterate_TLater_later i T ρ v:
    ⟦ iterate TLater i T ⟧ ρ v ≡ (▷^i ⟦ T ⟧ ρ v)%I.
  Proof.
    elim: i => [|i IHi] //.
    rewrite iterate_S /=; unfold_interp; rewrite IHi //.
  Qed.

  Lemma semantic_typing_uniform_step_index Γ T e i:
    Γ ⊨ e : T -∗ Γ ⊨ e : T,i.
  Proof.
    iIntros "#H !>" (ρ) "#HΓ".
    iInduction i as [|i] "IHi". by iApply "H". iExact "IHi".
  Qed.

  Lemma interp_env_lookup Γ ρ T x:
    Γ !! x = Some T →
    G⟦ Γ ⟧ ρ -∗ ⟦ (shiftN x T) ⟧ ρ (ρ x).
  Proof.
    elim: Γ ρ x => [//|τ' Γ' IHΓ] ρ x Hx /=.
    iDestruct 1 as "[Hg Hv]". move: x Hx => [ [->] | x Hx] /=.
    - rewrite hsubst_id. by [].
    - rewrite hrenS.
      iApply (interp_weaken_one (shiftN x T)).
      iApply (IHΓ ((+1) >>> ρ) x Hx with "Hg").
  Qed.

  Context {Γ}.
  Lemma Sub_Refl T i : Γ ⊨ T, i <: T, i.
  Proof. by iIntros "/= !> **". Qed.

  Lemma Sub_Trans T1 T2 T3 i1 i2 i3 : Γ ⊨ T1, i1 <: T2, i2 -∗
                                      Γ ⊨ T2, i2 <: T3, i3 -∗
                                      Γ ⊨ T1, i1 <: T3, i3.
  Proof.
    iIntros "#Hsub1 #Hsub2 /= !> * #Hg #HT".
    iApply ("Hsub2" with "Hg (Hsub1 Hg [//])").
  Qed.

  Lemma DSub_Refl T i : Γ ⊨[i] T <: T.
  Proof. by iIntros "/= !> ** !> **". Qed.

  Lemma DSub_Trans T1 T2 T3 i : Γ ⊨[i] T1 <: T2 -∗
                                Γ ⊨[i] T2 <: T3 -∗
                                Γ ⊨[i] T1 <: T3.
  Proof.
    iIntros "#Hsub1 #Hsub2 /= !> * #Hg".
    iSpecialize ("Hsub1" with "Hg"); iSpecialize ("Hsub2" with "Hg").
    iIntros "!>" (v) "#HT". iApply "Hsub2". by iApply "Hsub1".
  Qed.
End logrel_lemmas.
