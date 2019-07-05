From D Require Import iris_prelude swap_later_impl asubst_intf.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_language language.

From D.pure_program_logic Require adequacy.
From D Require gen_iheap saved_interp.

Module mapsto.
Export gen_iheap.

Notation "s ↦ γ" := (mapsto (L := stamp) s γ) (at level 20) : bi_scope.
Section mapsto_stamp_gname.
  Context `{gen_iheapG stamp gname Σ}.
  Global Instance: Persistent (s ↦ γ) := _.
  Global Instance: Timeless (s ↦ γ) := _.

  Definition allGs (gs : gmap stamp gname) := gen_iheap_ctx gs.
  Global Arguments allGs /.
End mapsto_stamp_gname.
End mapsto.

Module Type LiftWp (Import VS : VlSortsSig).
  Export mapsto saved_interp.
  Implicit Types (v : vl) (vs : vls) (Σ : gFunctors).

  Notation envPred s Σ := ((var → vl) -d> s -d> iProp Σ).
  Instance InhEnvPred s Σ : Inhabited (envPred s Σ) := populate (λ _ _, False)%I.
  Notation envD Σ := (envPred vl Σ).

  Class TyInterp ty Σ :=
    ty_interp : ty -> (var → vl) -> vl -> iProp Σ.

  Class dlangG Σ := DLangG {
    dlangG_savior :> savedInterpG Σ (var → vl) vl;
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

  Notation "s ↝ φ" := (∃ γ, s ↦ γ ∗ γ ⤇ φ)%I  (at level 20) : bi_scope.

  Definition stamp_σ_to_type `{!dlangG Σ} s σ (ψ : vl -d> iProp Σ) : iProp Σ :=
    (∃ φ : envD Σ, ⌜ ψ = φ (to_subst σ) ⌝ ∗ s ↝ φ)%I.
  Notation "s ↗[ σ  ] ψ" := (stamp_σ_to_type s σ ψ) (at level 20).

  Section mapsto.
    Context `{!dlangG Σ}.

    Global Instance stamp_σ_to_type_persistent σ s ψ: Persistent (s ↗[ σ  ] ψ) := _.

    Lemma stamp_σ_to_type_agree σ s ψ1 ψ2 v :
      s ↗[ σ ] ψ1 -∗ s ↗[ σ ] ψ2 -∗ ▷ (ψ1 v ≡ ψ2 v).
    Proof.
      iDestruct 1 as (φ1 -> γ1) "[Hs1 Hg1]".
      iDestruct 1 as (φ2 -> γ2) "[Hs2 Hg2]".
      iDestruct (mapsto_agree with "Hs1 Hs2") as %->.
      iApply (saved_interp_agree with "Hg1 Hg2").
    Qed.

    Lemma stamp_σ_to_type_intro s σ φ : s ↝ φ -∗ s ↗[ σ ] φ (to_subst σ).
    Proof. rewrite /stamp_σ_to_type. iIntros; iExists φ; auto. Qed.
  End mapsto.

  Module dlang_adequacy.
    Class dlangPreG Σ := DLangPreG {
      dlangPreG_savior :> savedInterpG Σ (var → vl) vl;
      dlangPreG_interpNames :> gen_iheapPreG stamp gname Σ;
    }.
    Definition dlangΣ := #[savedInterpΣ (var → vl) vl; gen_iheapΣ stamp gname].

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
