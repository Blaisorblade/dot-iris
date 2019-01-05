From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import tactics.
From Dot Require Export operational tactics.

(** Deduce types from variable names, like on paper, for readability and to help
    type inference for some overloaded operations (e.g. substitution). *)
Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms)
         (Γ : ctx) (ρ : leibnizC vls).


(** The logical relation core is the [interp], interprets *open* types into
    predicates over *closed* values. Hence, [interp T ρ v] uses its argument [ρ]
    to interpret anything contained in T, but not things contained in v.

    Semantic judgements must apply instead to open terms/value/paths; therefore,
    they are defined using closing substitution on arguments of [interp].

    Similar comments apply to [def_interp].

    Additionally, both apply to *translated* arguments, hence they only expect
    [dtysem] and not [dtysyn] for type member definitions.
 *)
Section logrel.
  Context `{dotG Σ}.

  (* Use Program without its extended pattern-matching compiler; we only need
     its handling of coercions. *)
  Unset Program Cases.

  Notation D := (vlC -n> iProp Σ).
  Implicit Types τi : D.

  Program Definition def_interp_vmem (interp : listVlC -n> D) :
    listVlC -n> dmC -n> iProp Σ :=
    λne ρ d, (⌜ nclosed d 0 ⌝ ∗ ∃ vmem, ⌜d = dvl vmem⌝ ∧ ▷ interp ρ vmem)%I.

  Program Definition interp_vmem l (interp : listVlC -n> D) : listVlC -n> D :=
    λne ρ v, (⌜ nclosed_vl v 0 ⌝ ∗ ∃ d, ⌜v @ l ↘ d⌝ ∧ def_interp_vmem interp ρ d)%I.

  Definition idm_proj_semtype d σ (φ : listVlC -n> D) : iProp Σ :=
    (∃ γ, ⌜ d = dtysem σ γ ⌝ ∗ γ ⤇ (λ vs w, φ vs w))%I.
  Global Arguments idm_proj_semtype /.
  Notation "d ↗ σ , φ" := (idm_proj_semtype d σ φ) (at level 20).

  Program Definition def_interp_tmem (interp1 interp2 : listVlC -n> D) :
    listVlC -n> dmC -n> iProp Σ :=
    λne ρ d,
    (⌜ nclosed d 0 ⌝ ∗ ∃ φ σ, (d ↗ σ , φ) ∗
       □ ((∀ v, ⌜ nclosed_vl v 0 ⌝ → ▷ interp1 ρ v → ▷ □ φ σ v) ∗
          (∀ v, ⌜ nclosed_vl v 0 ⌝ → ▷ □ φ σ v → ▷ interp2 ρ v) ∗
          (∀ v, interp1 ρ v → interp2 ρ v)))%I.

  Program Definition interp_tmem l (interp1 interp2 : listVlC -n> D) : listVlC -n> D :=
    λne ρ v,
    (⌜ nclosed_vl v 0 ⌝ ∗ ∃ d, ⌜ v @ l ↘ d ⌝ ∧ def_interp_tmem interp1 interp2 ρ d)%I.

  Program Definition interp_expr (φ : listVlC -n> D) : listVlC -n> tmC -n> iProp Σ :=
    λne ρ t, WP t {{ φ ρ }} %I.

  Program Definition interp_and (interp1 interp2 : listVlC -n> D): listVlC -n> D :=
    λne ρ v, (interp1 ρ v ∧ interp2 ρ v) %I.

  Program Definition interp_or (interp1 interp2 : listVlC -n> D) : listVlC -n> D :=
    λne ρ v, (interp1 ρ v ∨ interp2 ρ v) %I.

  Program Definition interp_later (interp : listVlC -n> D) : listVlC -n> D :=
    λne ρ v, (⌜ nclosed_vl v 0 ⌝ ∗ ▷ (interp ρ v)) % I.

  Program Definition interp_nat : listVlC -n> D := λne ρ v, (∃ n, ⌜v = vnat n⌝) %I.

  Program Definition interp_top : listVlC -n> D := λne ρ v, ⌜ nclosed_vl v 0 ⌝%I.

  Program Definition interp_bot : listVlC -n> D := λne ρ v, False%I.

  (* XXX Paolo: This definition is correct but non-expansive; I suspect we might
     need to readd later here, but also to do the beta-reduction in place, to
     make it contractive (similarly to what's useful for equi-recursive types).
     However, I am not totally sure and might be wrong; it'd be good to
     write an example where this makes a difference.
     I think that would be something like
     nu x. { T = TNat; U = x.T -> x.T }:
     mu (x: {T <: TNat; U <: x.T -> TNat}).
     If the function type constructor is not contractive but only non-expansive,
     typechecking this example needs to establish x.T <: TNat having in context
     only x: {T <: TNat; U <: x.T -> TNat}.
   *)
  Program Definition interp_forall (interp1 interp2 : listVlC -n> D) : listVlC -n> D :=
    λne ρ v,
    (⌜ nclosed_vl v 0 ⌝ ∗ □ ∀ w, interp1 ρ w -∗ interp_expr interp2 (w :: ρ) (tapp (tv v) (tv w)))%I.

  Program Definition interp_mu (interp : listVlC -n> D) : listVlC -n> D :=
    λne ρ v, interp (v::ρ) v.

  (** A simplified variant of weakest preconditions for path evaluation.
      The difference is that path evaluation is completely pure, and
      postconditions must hold now, not after updating resources.
      vp ("Value from Path") and vq range over results of evaluating paths.

      Path evaluation was initially more complex; now that we got to this
      version, I wonder whether we can just use the standard Iris WP, but I am
      not sure if that would work.
      *)
  Fixpoint path_wp p (interp_k: D): iProp Σ :=
    match p with
    | pself p l => path_wp p (λne vp, ∃ vq, ⌜ vp @ l ↘ dvl vq ⌝ ∧ ▷ interp_k vq)
    | pv vp => interp_k vp
    end%I.

  Global Instance path_wp_persistent (pred: D) p:
    (forall (vp: vl), Persistent (pred vp)) →
    Persistent (path_wp p pred).
  Proof. elim: p pred => *; apply _. Qed.

  Program Definition interp_selA (p: path) (l: label) (interpL interpU : listVlC -n> D) :
    listVlC -n> D :=
    λne ρ v,
    (interpU ρ v ∧ (interpL ρ v ∨
                    path_wp p.|[to_subst ρ]
                            (λne vp, ∃ σ ϕ d, ⌜vp @ l ↘ d⌝ ∧ d ↗ σ , ϕ ∧ ▷ □ ϕ σ v)))%I.

  Definition interp_sel (p: path) (l: label) : listVlC -n> D :=
    interp_selA p l interp_bot interp_top.

  Fixpoint interp (T: ty) : listVlC -n> D :=
    match T with
    | TTMem l L U => interp_tmem l (interp L) (interp U)
    | TVMem l T' => interp_vmem l (interp T')
    | TAnd T1 T2 => interp_and (interp T1) (interp T2)
    | TOr T1 T2 => interp_or (interp T1) (interp T2)
    | TLater T => interp_later (interp T)
    | TNat => interp_nat
    | TTop => interp_top
    | TBot => interp_bot
    | TAll T1 T2 => interp_forall (interp T1) (interp T2)
    | TMu T => interp_mu (interp T)
    | TSel p l => interp_sel p l
    | TSelA p l L U => interp_selA p l (interp L) (interp U)
  end % I.

  Global Instance dotInterpΣ : dotInterpG Σ := DotInterpG _ (λ T ρ, interp T ρ).
  Notation "⟦ T ⟧" := (interp T).

  Global Instance interp_persistent T ρ v :
    Persistent (⟦ T ⟧ ρ v).
  Proof. revert v ρ; induction T => v ρ; simpl; try apply _. Qed.

  Program Fixpoint def_interp (T: ty) (l : label) :
    listVlC -n> dmC -n> iProp Σ :=
    λne ρ d,
    match T with
    | TTMem l' L U => ⌜ l = l' ⌝ ∧ def_interp_tmem (interp L) (interp U) ρ d
    | TVMem l' T' => ⌜ l = l' ⌝ ∧ def_interp_vmem (interp T') ρ d
    | _ => False
    end%I.

  Global Instance def_interp_persistent T l ρ d :
    Persistent (def_interp T l ρ d).
  Proof. revert ρ d; induction T; simpl; try apply _. Qed.

  Program Definition defs_interp_and
             (interp1 : listVlC -n> dmsC -n> iProp Σ)
             (interp2: label -> listVlC -n> dmC -n> iProp Σ)
    : listVlC -n> dmsC -n> iProp Σ :=
    λne ρ ds,
    match ds with
    | [] => False
    | d :: ds => interp1 ρ ds ∧ interp2 (length ds) ρ d
    end%I.

  Program Fixpoint defs_interp (T: ty) : listVlC -n> dmsC -n> iProp Σ :=
    match T with
    | TAnd T1 T2 => defs_interp_and (defs_interp T1) (def_interp T2)
    | TTop => λne ρ ds, ⌜ nclosed ds 0 ⌝
    | _ => λne ρ ds, False
    end % I.

  Global Instance defs_interp_persistent T ρ ds :
    Persistent (defs_interp T ρ ds).
  Proof.
    revert ds ρ; induction T; simpl; intros; try case_match; try apply _.
  Qed.

  Fixpoint interp_env (Γ : ctx) (vs : vls) : iProp Σ :=
    match Γ with
    | nil => ⌜vs = nil⌝
    | T :: Γ' =>
      match vs with
      | nil => False
      | v :: ρ => interp_env Γ' ρ ∗ ⟦ T ⟧ (v::ρ) v
      end
    end%I.

  Notation "⟦ Γ ⟧*" := (interp_env Γ).

  Global Instance interp_env_persistent Γ ρ :
    Persistent (⟦ Γ ⟧* ρ) := _.
  Proof.
    revert ρ. induction Γ.
    - rewrite /Persistent /interp_env. eauto.
    - simpl. destruct ρ; rewrite /Persistent; eauto.
  Qed.

  (** Definitions for semantic (definition) (sub)typing *)
  (** Since [⟦Γ⟧* ρ] might be impossible, we must require closedness explicitly. *)
  Definition idtp Γ T l d : iProp Σ :=
    (⌜ nclosed d (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ → def_interp T l ρ d.|[to_subst ρ])%I.
  Global Arguments idtp /.
  Notation "Γ ⊨d { l = d } : T" := (idtp Γ T l d) (at level 64, l, d, T at next level).

  Lemma idtp_closed Γ T l d: (Γ ⊨d {l = d} : T → ⌜ nclosed d (length Γ) ⌝)%I.
  Proof. iIntros "[$ _]". Qed.

  Definition idstp Γ T ds : iProp Σ :=
    (⌜ nclosed ds (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ → defs_interp T ρ ds.|[to_subst ρ])%I.
  Global Arguments idstp /.
  Notation "Γ ⊨ds ds : T" := (idstp Γ T ds) (at level 74, ds, T at next level).

  Lemma idstp_closed Γ T ds: (Γ ⊨ds ds : T → ⌜ nclosed ds (length Γ) ⌝)%I.
  Proof. iIntros "[$ _]". Qed.

  Notation "⟦ T ⟧ₑ" := (interp_expr (interp T)).

  (* Really needed? Try to stop using it. *)
  Definition ivtp Γ T v : iProp Σ := (⌜ nclosed_vl v (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ → ⟦T⟧ ρ v.[to_subst ρ])%I.
  Global Arguments ivtp /.

  Definition ietp Γ T e : iProp Σ := (⌜ nclosed e (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ → ⟦T⟧ₑ ρ (e.|[to_subst ρ]))%I.
  Global Arguments ietp /.
  Notation "Γ ⊨ e : T" := (ietp Γ T e) (at level 74, e, T at next level).

  Lemma ietp_closed Γ T e: (Γ ⊨ e : T → ⌜ nclosed e (length Γ) ⌝)%I.
  Proof. iIntros "[$ _]". Qed.

  Definition step_indexed_ietp Γ T e i: iProp Σ :=
    (⌜ nclosed e (length Γ) ⌝ ∗ □∀ ρ, ⟦Γ⟧* ρ → ▷^i ⟦T⟧ₑ ρ (e.|[to_subst ρ]))%I.
  Global Arguments step_indexed_ietp /.
  Notation "Γ ⊨ e : T , i" := (step_indexed_ietp Γ T e i) (at level 74, e, T at next level).

  Lemma step_indexed_ietp_closed Γ T e i: (Γ ⊨ e : T, i → ⌜ nclosed e (length Γ) ⌝)%I.
  Proof. iIntros "[$ _]". Qed.

  (** Subtyping. Defined on values. *)
  Definition ivstp Γ T1 T2: iProp Σ := (□∀ ρ v, ⟦Γ⟧* ρ → ⟦T1⟧ ρ v → ⟦T2⟧ ρ v)%I.
  Global Arguments ivstp /.

  (** Indexed Subtyping. Defined on closed values. We must require closedness
      explicitly, since closedness now does not follow from being well-typed later. *)
  Definition step_indexed_ivstp Γ T1 T2 i j: iProp Σ :=
    (□∀ ρ v, ⌜ nclosed_vl v 0 ⌝ → ⟦Γ⟧*ρ → (▷^i ⟦T1⟧ ρ v) → ▷^j ⟦T2⟧ ρ v)%I.
  Global Arguments step_indexed_ivstp /.

  Global Instance idtp_persistent Γ T l d: Persistent (idtp Γ T l d) := _.
  Global Instance idstp_persistent Γ T ds: Persistent (idstp Γ T ds) := _.
  Global Instance ietp_persistent Γ T e : Persistent (ietp Γ T e) := _.
  Global Instance step_indexed_ietp_persistent Γ T e i : Persistent (step_indexed_ietp Γ T e i) := _.
  Global Instance step_indexed_ivstp_persistent Γ T1 T2 i j : Persistent (step_indexed_ivstp Γ T1 T2 i j) := _.
  Global Instance ivstp_persistent Γ T1 T2 : Persistent (ivstp Γ T1 T2) := _.
End logrel.

Notation "⟦ T ⟧" := (interp T).
Notation "⟦ Γ ⟧*" := (interp_env Γ).
Notation "⟦ T ⟧ₑ" := (interp_expr (interp T)).

(** Single-definition typing *)
Notation "Γ ⊨d { l = d } : T" := (idtp Γ T l d) (at level 64, l, d, T at next level).
(** Multi-definition typing *)
Notation "Γ ⊨ds ds : T" := (idstp Γ T ds) (at level 74, ds, T at next level).
(** Expression typing *)
Notation "Γ ⊨ e : T" := (ietp Γ T e) (at level 74, e, T at next level).
(** Indexed expression typing *)
Notation "Γ ⊨ e : T , i" := (step_indexed_ietp Γ T e i) (at level 74, e, T at next level).

Notation "Γ ⊨ T1 <: T2" := (ivstp Γ T1 T2) (at level 74, T1, T2 at next level).
Notation "Γ '⊨' '[' T1 ',' i ']' '<:' '[' T2 ',' j ']'" := (step_indexed_ivstp Γ T1 T2 i j) (at level 74, T1, T2 at next level).

Section logrel_lemmas.
  Context `{HdotG: dotG Σ}.

  Lemma iterate_TLater_later i T ρ v:
    nclosed_vl v 0 →
    ⟦ iterate TLater i T ⟧ ρ v ≡ (▷^i ⟦ T ⟧ ρ v)%I.
  Proof.
    elim: i => [|i IHi] // => Hcl. rewrite iterate_S /= IHi //.
    iSplit; by [iIntros "#[_ $]" | iIntros "$"].
  Qed.

  Context Γ.

  Lemma semantic_typing_uniform_step_index T e i:
    (Γ ⊨ e : T → Γ ⊨ e : T,i)%I.
  Proof.
    iIntros "[$ #H] !>" (ρ) "#HΓ".
    iInduction i as [|i] "IHi". by iApply "H". iApply "IHi".
  Qed.

  Lemma interp_v_closed T v ρ: (interp T ρ v → ⌜ nclosed_vl v 0 ⌝)%I.
  Proof.
    iInduction T as [] "IHT" forall (ρ v); iIntros "#HT //="; try by (iDestruct "HT" as "[% _]").
    - iDestruct "HT" as "[#HT1 #HT2]". by iApply "IHT".
    - iDestruct "HT" as "[#HT1 | #HT2]"; by [iApply "IHT" | iApply "IHT1"].
    - by iApply "IHT".
    - iDestruct "HT" as "[#HT2 _]". by iApply "IHT1".
    - by iDestruct "HT" as (n) "->".
  Qed.

  Lemma interp_env_len_agree ρ:
    (⟦ Γ ⟧* ρ → ⌜ length ρ = length Γ ⌝)%I.
  Proof.
    iInduction Γ as [|τ Γ'] "IHΓ" forall (ρ); destruct ρ => //=.
    iIntros "#[HG Hv]".
    by iDestruct ("IHΓ" $! ρ with "HG") as "->".
  Qed.

  Lemma interp_env_ρ_closed ρ: (⟦ Γ ⟧* ρ → ⌜ cl_ρ ρ ⌝)%I.
  Proof.
    revert Γ ρ. elim => [|T Γ IHl] [|v ρ] /=; try (by iIntros "%").
    iIntros "[#HG #HT]".
    iPoseProof (interp_v_closed with "HT") as "%".
    iPoseProof (IHl with "HG") as "%".
    iPureIntro; by constructor.
  Qed.

End logrel_lemmas.
