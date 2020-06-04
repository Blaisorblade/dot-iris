(** * Instantiate Iris for D* languages. *)
From iris.program_logic Require Import ectx_language language.
From iris.base_logic.lib Require Import own.
From D.pure_program_logic Require adequacy.
From D Require Import iris_prelude swap_later_impl asubst_intf.
From D Require saved_interp_dep.
From D.iris_extra Require det_reduction.

Set Suggest Proof Using.
Set Default Proof Using "Type".

Module Type LiftWp (Import VS : VlSortsSig).
  Export prelude saved_interp_dep.
  Implicit Types (v : vl) (vs : vls) (Σ : gFunctors).
  Include SavedInterpDep VS.

  Notation savedHoSemTypeG Σ := (savedHoEnvPredG vl Σ).
  Notation savedHoSemTypeΣ := (savedHoEnvPredΣ vl).

  Instance InhEnvPred s Σ : Inhabited (envPred s Σ) := populate (λI _ _, False).

  (** ** Define Iris ghost state used by gD<:/gDOT proofs.
  Iris proofs must abstract over instances of [dlangG Σ].
  For further details, see
  https://gitlab.mpi-sws.org/iris/iris/-/blob/ffacaa0337d6668dc11646b330c114184d258b76/docs/proof_guide.md#resource-algebra-management.
  *)
  Class dlangG Σ `{InhabitedState dlang_lang} := DLangG {
    dlangG_savior :> savedHoSemTypeG Σ;
    dlangG_langdet :> LangDet dlang_lang;
  }.
  Arguments DLangG _ {_ _ _}.

  (** ** Instance of [irisG] enable using the expression weakest precondition; this instance. *)
  Instance dlangG_irisG `{dlangG Σ} : irisG dlang_lang Σ := {
    irisG_langdet := _;
  }.

  (** Notation [s ↝n[ n  ] φ] generalizes [s ↝ φ] on paper; [n] is the arity. *)
  Definition leadsto_n `{dlangG Σ}
    s n (φ : hoEnvD Σ n) : iProp Σ := s ⤇n[ n ] φ.
  Notation "s ↝n[ n  ] φ" := (leadsto_n s n φ) (at level 20) : bi_scope.

  Program Definition hoEnvD_inst {i Σ} σ : hoEnvD Σ i -n> hoD Σ i :=
    λne φ, λ args, φ args (∞ σ).
  Next Obligation. move => i Σ σ n x y Heq args. exact: Heq. Qed.

  Definition stamp_σ_to_type_n `{dlangG Σ} s σ n (ψ : hoD Σ n) : iProp Σ :=
    ∃ φ : hoEnvD Σ n, s ↝n[ n ] φ ∧ ▷ (ψ ≡ hoEnvD_inst σ φ).
  Notation "s ↗n[ σ , n  ] ψ" := (stamp_σ_to_type_n s σ n ψ) (at level 20): bi_scope.

  (* Beware: to prove [sD_Typ_Abs], here we must use [∞ σ.|[ρ]], not [∞ σ >> ρ]. *)
  Definition leadsto_envD_equiv `{dlangG Σ} {i} s σ (φ : hoEnvD Σ i) : iProp Σ :=
    ∃ (φ' : hoEnvD Σ i),
      ⌜φ ≡ (λ args ρ, φ' args (∞ σ.|[ρ]))⌝ ∧ s ↝n[ i ] φ'.
  Arguments leadsto_envD_equiv /.
  Notation "s ↝[ σ  ] φ" := (leadsto_envD_equiv s σ φ) (at level 20).

  Section mapsto.
    Context `{Hdlang : dlangG Σ}.

    Global Instance: Contractive (leadsto_n s n).
    Proof. solve_contractive. Qed.

    Global Instance: Persistent (s ↝n[ n ] φ) := _.

    Global Instance: Contractive (stamp_σ_to_type_n s σ i).
    Proof. rewrite /stamp_σ_to_type_n. solve_contractive_ho. Qed.

    Import EqNotations.
    Lemma leadsto_agree_dep_abs {s n1 n2 φ1 φ2} :
      s ↝n[ n1 ] φ1 -∗ s ↝n[ n2 ] φ2 -∗ ∃ Heq : n1 = n2,
        ▷ ((rew [hoEnvD Σ] Heq in φ1) ≡ φ2).
    Proof. apply saved_ho_sem_type_agree_dep_abs. Qed.

    Lemma leadsto_agree_dep {s n1 n2 φ1 φ2} args ρ v :
      s ↝n[ n1 ] φ1 -∗ s ↝n[ n2 ] φ2 -∗ ∃ Heq : n1 = n2,
        ▷ ((rew [hoEnvD Σ] Heq in φ1) args ρ v ≡ φ2 args ρ v).
    Proof. apply saved_ho_sem_type_agree_dep. Qed.

    Lemma leadsto_agree {s n φ1 φ2} args ρ v :
      s ↝n[ n ] φ1 -∗ s ↝n[ n ] φ2 -∗ ▷ (φ1 args ρ v ≡ φ2 args ρ v).
    Proof. apply saved_ho_sem_type_agree. Qed.

    Lemma leadsto_alloc {i} (φ : hoEnvD Σ i) :
      ⊢ |==> ∃ s, s ↝n[ i ] φ.
    Proof. apply saved_ho_sem_type_alloc. Qed.

    Global Opaque leadsto_n.

    Lemma stamp_σ_to_type_agree_dep_abs {σ s n1 n2 ψ1 ψ2} :
      s ↗n[ σ , n1 ] ψ1 -∗ s ↗n[ σ , n2 ] ψ2 -∗ ∃ Heq : n1 = n2,
        ▷ ((rew [hoD Σ] Heq in ψ1) ≡ ψ2).
    Proof.
      iDestruct 1 as (φ1) "[Hsg1 Heq1]"; iDestruct 1 as (φ2) "[Hsg2 Heq2]".
      iDestruct (leadsto_agree_dep_abs with "Hsg1 Hsg2") as (->) "Hgoal".
      iExists eq_refl. iNext.
      iEval (cbn) in "Hgoal"; iEval (cbn). iRewrite "Heq1"; iRewrite "Heq2".
      repeat setoid_rewrite discrete_fun_equivI.
      iIntros (??) "/=". iExact "Hgoal".
    Qed.

    Lemma stamp_σ_to_type_agree_dep {σ s n1 n2 ψ1 ψ2} args v :
      s ↗n[ σ , n1 ] ψ1 -∗ s ↗n[ σ , n2 ] ψ2 -∗ ∃ Heq : n1 = n2,
        ▷ ((rew [hoD Σ] Heq in ψ1) args v ≡ ψ2 args v).
    Proof.
      iIntros "H1 H2".
      iDestruct (stamp_σ_to_type_agree_dep_abs with "H1 H2") as (->) "Hgoal".
      iExists eq_refl; cbn; iNext.
      by repeat setoid_rewrite discrete_fun_equivI.
    Qed.

    Lemma stamp_σ_to_type_agree {σ s n ψ1 ψ2} args v :
      s ↗n[ σ , n ] ψ1 -∗ s ↗n[ σ , n ] ψ2 -∗ ▷ (ψ1 args v ≡ ψ2 args v).
    Proof.
      iIntros "Hs1 Hs2".
      iDestruct (stamp_σ_to_type_agree_dep args v with "Hs1 Hs2") as (Heq) "H".
      by rewrite (proof_irrel Heq eq_refl) /=.
    Qed.

    Lemma stamp_σ_to_type_intro s σ n (φ : hoEnvD Σ n) :
      s ↝n[ n ] φ -∗ s ↗n[ σ , n ] hoEnvD_inst σ φ.
    Proof. rewrite /stamp_σ_to_type_n. iIntros; iExists φ; auto. Qed.

    Global Instance stamp_σ_to_type_persistent σ s n ψ : Persistent (s ↗n[ σ , n ] ψ) := _.
  End mapsto.

  Global Opaque stamp_σ_to_type_n.

  Module dlang_adequacy.
    Class dlangPreG Σ := DLangPreG {
      dlangPreG_savior :> savedHoSemTypeG Σ;
    }.
    Definition dlangΣ := #[savedHoSemTypeΣ].

    Instance subG_dlangΣ {Σ} : subG dlangΣ Σ → dlangPreG Σ.
    Proof. solve_inG. Qed.

    Instance CmraSwappable_dlang: CmraSwappable (iResUR dlangΣ).
    Proof.
      apply Swappable_iResUR; rewrite /gid /=.
      apply fin_S_inv; cbn; first apply _.
      apply fin_0_inv.
    Qed.
    Export adequacy det_reduction.

    Section LangDet.
    Context `{LangDet dlang_lang}.

    Lemma adequate_safe (e : expr dlang_lang):
      adequate e (λ _, True) → safe e.
    Proof. intros [_ Had] ** ?. exact: Had. Qed.

    (* [Himpl] only takes explicit arguments because Coq doesn't support
    implicit ones. *)
    Theorem adequacy_dlang Σ `{dlangPreG Σ} `{SwapPropI Σ} e
      (Φ : dlangG Σ → val dlang_lang → iProp Σ)
      (Ψ : val dlang_lang → Prop)
      (Himpl : ∀ (Hdlang : dlangG Σ) v, Φ Hdlang v -∗ ⌜Ψ v⌝)
      (Hwp : ∀ (Hdlang : dlangG Σ) `(!SwapPropI Σ), ⊢ WP e {{ v, Φ Hdlang v }}) :
      adequate e (λ v, Ψ v).
    Proof.
      apply (wp_adequacy (Σ := Σ) (Λ := dlang_lang) e Ψ) => /=.
      set (DLangΣ := DLangG Σ).
      iIntros "!>".
      iDestruct (Hwp DLangΣ) as "Hwp".
      iApply (wp_wand with "Hwp"). by iIntros (v); iApply Himpl.
    Qed.

    Corollary safety_dlang Σ `{dlangPreG Σ} `{SwapPropI Σ}
      (Φ : dlangG Σ → val dlang_lang → iProp Σ) e
      (Hwp : ∀ (Hdlang : dlangG Σ) `(!SwapPropI Σ), ⊢ WP e {{ Φ Hdlang }}):
      safe e.
    Proof. apply adequate_safe, (adequacy_dlang Σ e Φ), Hwp; naive_solver. Qed.
    End LangDet.
  End dlang_adequacy.

  (* Backward compatibility. *)
  Notation "s ↝ φ" := (s ↝n[ 0 ] vopen φ)%I  (at level 20) : bi_scope.
  Notation "s ↗[ σ  ] ψ" := (s ↗n[ σ , 0 ] vopen ψ)%I (at level 20) : bi_scope.
End LiftWp.
