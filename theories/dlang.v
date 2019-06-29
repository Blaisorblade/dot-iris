From D Require Import iris_prelude swap_later_impl asubst_intf.
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

Module Type LiftWp (Import values: Values) (Import sorts: SortsIntf values).
  Export mapsto saved_interp weakestpre.
  Implicit Types (v : vl) (ρ vs : vls) (Σ : gFunctors).

  Notation envD Σ := (vls -d> vl -d> iProp Σ).
  Instance Inhϕ: Inhabited (envD Σ).
  Proof. constructor. exact (λ _ _, False)%I. Qed.

  Class TyInterp ty Σ :=
    ty_interp : ty -> vls -> vl -> iProp Σ.

  Class dlangG Σ := DLangG {
    dlangG_savior :> savedInterpG Σ vls vl;
    dlangG_interpNames :> gen_iheapG stamp gname Σ;
  }.

  Instance dlangG_irisG `{dlangG Σ} : irisG dlang_lang Σ := {
    state_interp σ κs _ := True%I;
    fork_post _ := True%I;
  }.

  (* Defining this needs the above irisG instance in scope. *)
  Definition test_interp_expr `{dlangG Σ} :=
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

  Section mapsto.
    Context `{!dlangG Σ}.

    Lemma leadsto_agree s (φ1 φ2: envD Σ) ρ v: s ↝ φ1 -∗ s ↝ φ2 -∗ ▷ (φ1 ρ v ≡ φ2 ρ v).
    Proof.
      iIntros "/= #H1 #H2".
      iDestruct "H1" as (γ1) "[Hs1 Hg1]".
      iDestruct "H2" as (γ2) "[Hs2 Hg2]".
      iDestruct (mapsto_agree with "Hs1 Hs2") as %->.
      by iApply (saved_interp_agree _ φ1 φ2).
    Qed.
  End mapsto.

  Module dlang_adequacy.
    Class dlangPreG Σ := DLangPreG {
      dlangPreG_savior :> savedInterpG Σ vls vl;
      dlangPreG_interpNames :> gen_iheapPreG stamp gname Σ;
    }.
    Definition dlangΣ := #[savedInterpΣ vls vl; gen_iheapΣ stamp gname].

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
