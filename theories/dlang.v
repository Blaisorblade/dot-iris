From D Require Import iris_prelude swap_later_impl asubst_intf.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_language language.

From D.pure_program_logic Require adequacy.
From D Require gen_iheap saved_interp_dep.

Module mapsto.
Export gen_iheap.

Notation "s ↦ γ" := (mapsto (L := stamp) s γ) (at level 20) : bi_scope.
Notation allGs gs := (gen_iheap_ctx (L := stamp) gs).

Section mapsto_stamp_gname.
  Context `{gen_iheapG stamp gname Σ}.
  Global Instance: Persistent (s ↦ γ) := _.
  Global Instance: Timeless (s ↦ γ) := _.
End mapsto_stamp_gname.
End mapsto.

Module Type LiftWp (Import VS : VlSortsSig).
  Export mapsto saved_interp_dep.
  Implicit Types (v : vl) (vs : vls) (Σ : gFunctors).
  Include SavedInterpDep VS.

  Notation savedHoSemTypeG Σ := (savedHoEnvPredG vl Σ).
  Notation savedHoSemTypeΣ := (savedHoEnvPredΣ vl).

  Instance InhEnvPred s Σ : Inhabited (envPred s Σ) := populate (λ _ _, False)%I.

  Class TyInterp ty Σ :=
    ty_interp : ty -> envD Σ.
  Notation "⟦ T ⟧" := (ty_interp T).

  (* Also appears in Autosubst.*)
  Global Arguments ty_interp {_ _ _} !_ /.

  Class dlangG Σ := DLangG {
    dlangG_savior :> savedHoSemTypeG Σ;
    dlangG_interpNames :> gen_iheapG stamp gname Σ;
  }.

  Instance dlangG_irisG `{dlangG Σ} : irisG dlang_lang Σ := {
    state_interp σ κs _ := True%I;
    fork_post _ := True%I;
  }.

  (* Defining this needs the above irisG instance in scope. *)
  Local Definition test_interp_expr `{dlangG Σ} :=
    λ (t: expr dlang_lang), WP t {{ v, False }} %I.

  (* Copied from F_mu *)
  Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
  Hint Extern 10 (IntoVal _ _) =>
    rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

  Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) constr(Hv) uconstr(Hp) :=
    iApply (wp_bind (fill[ctx]));
    iApply (wp_wand with "[-]"); [iApply Hp; trivial|]; cbn;
    iIntros (v) Hv.

  Definition stamp_to_type_n `{!dlangG Σ}
    s n (φ : hoEnvD Σ n) := (∃ γ, (s ↦ γ) ∗ γ ⤇n[ n ] φ)%I.
  Notation "s ↝n[ n  ] φ" := (stamp_to_type_n s n φ) (at level 20) : bi_scope.

  Definition hoEnvD_inst {n Σ} (φ : hoEnvD Σ n) σ : hoD Σ n := λ args, φ args (to_subst σ).

  Definition stamp_σ_to_type_n `{!dlangG Σ} s σ n (ψ : hoD Σ n) : iProp Σ :=
    (∃ φ : hoEnvD Σ n, ⌜ ψ = hoEnvD_inst φ σ ⌝ ∗ s ↝n[ n ] φ)%I.
  Notation "s ↗n[ σ , n  ] ψ" := (stamp_σ_to_type_n s σ n ψ) (at level 20): bi_scope.

  Notation "γ ⤇ φ" := (γ ⤇n[ 0 ] vopen φ) (at level 20).
  Notation "s ↝ φ" := (s ↝n[ 0 ] vopen φ)%I  (at level 20) : bi_scope.
  Notation "s ↗[ σ  ] ψ" := (s ↗n[ σ , 0 ] vopen ψ)%I (at level 20) : bi_scope.

  Section mapsto.
    Context `{!dlangG Σ}.

    Global Instance: Persistent (s ↝n[ n ] φ) := _.

    Global Instance stamp_σ_to_type_persistent σ s n ψ : Persistent (s ↗n[ σ , n ] ψ) := _.

    Lemma stamp_σ_to_type_agree_dep_arity {σ s n1 n2 ψ1 ψ2} :
      s ↗n[ σ , n1 ] ψ1 -∗ s ↗n[ σ , n2 ] ψ2 -∗ ⌜ n1 = n2 ⌝.
    Proof.
      iDestruct 1 as (φ1 -> γ1) "[Hs1 Hg1]".
      iDestruct 1 as (φ2 -> γ2) "[Hs2 Hg2]".
      iDestruct (mapsto_agree with "Hs1 Hs2") as %->.
      iDestruct (saved_ho_sem_type_agree_arity with "Hg1 Hg2") as %->.
      by [].
    Qed.

    Import EqNotations.
    Lemma stamp_σ_to_type_agree_dep {σ s n1 n2 ψ1 ψ2} args v :
      s ↗n[ σ , n1 ] ψ1 -∗ s ↗n[ σ , n2 ] ψ2 -∗ ∃ eq : n1 = n2,
        ▷ ((rew [hoD Σ] eq in ψ1) args v ≡ ψ2 args v).
    Proof.
      iDestruct 1 as (φ1 -> γ1) "[Hs1 Hg1]".
      iDestruct 1 as (φ2 -> γ2) "[Hs2 Hg2]".
      iDestruct (mapsto_agree with "Hs1 Hs2") as %->.
      iDestruct (saved_ho_sem_type_agree_arity with "Hg1 Hg2") as %->.
      iExists eq_refl; cbn.
      iApply (saved_ho_sem_type_agree with "Hg1 Hg2").
    Qed.

    Lemma stamp_σ_to_type_agree {σ s n ψ1 ψ2} args v :
      s ↗n[ σ , n ] ψ1 -∗ s ↗n[ σ , n ] ψ2 -∗ ▷ (ψ1 args v ≡ ψ2 args v).
    Proof.
      iIntros "Hs1 Hs2".
      iDestruct (stamp_σ_to_type_agree_dep args v with "Hs1 Hs2") as (eq) "H".
      rewrite (proof_irrel eq eq_refl) /=. by [].
    Qed.

    Lemma stamp_σ_to_type_intro s σ n (φ : hoEnvD Σ n) :
      s ↝n[ n ] φ -∗ s ↗n[ σ , n ] hoEnvD_inst φ σ.
    Proof. rewrite /stamp_σ_to_type_n. iIntros; iExists φ; auto. Qed.
  End mapsto.

  Global Opaque stamp_σ_to_type_n.

  Module dlang_adequacy.
    Class dlangPreG Σ := DLangPreG {
      dlangPreG_savior :> savedHoSemTypeG Σ;
      dlangPreG_interpNames :> gen_iheapPreG stamp gname Σ;
    }.
    Definition dlangΣ := #[savedHoSemTypeΣ; gen_iheapΣ stamp gname].

    Instance subG_dlangΣ {Σ} : subG dlangΣ Σ → dlangPreG Σ.
    Proof. solve_inG. Qed.

    Instance CmraSwappable_dlang: CmraSwappable (iResUR dlangΣ).
    Proof.
      apply Swappable_iResUR.
      rewrite /gid; repeat (dependent destruction i; cbn; try apply _).
    Qed.
    Import adequacy.

    Theorem adequacy Σ `{Sort (expr Λ)}
      `{HdlangG: dlangPreG Σ} `{SwapProp (iPropSI Σ)}
      (Φ : dlangG Σ → val dlang_lang → iProp Σ) e e' thp σ σ':
      (forall {Hdlang: dlangG Σ} `{SwapProp (iPropSI Σ)}, allGs ∅ ⊢ |==> □ WP e {{ Φ Hdlang }} ) →
      rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
      is_Some (to_val e') ∨ reducible e' σ'.
    Proof.
      intros Hlog ??. cut (adequate NotStuck e σ (λ _ _, True)); first (move => [_ ?]; by eauto).
      eapply (wp_adequacy Σ) => /=.
      iMod (gen_iheap_init (L := stamp) ∅) as (g) "Hgs".
      set (DLangΣ := DLangG Σ _ g).
      iMod (Hlog _ with "Hgs") as "#Hlog".
      iIntros (?) "!>". iExists (λ _ _, True%I); iSplit=> //.
      iApply wp_wand; by [iApply "Hlog" | auto].
    Qed.
  End dlang_adequacy.
End LiftWp.
