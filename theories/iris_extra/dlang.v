(** * Instantiate Iris for D* languages. *)
From iris.program_logic Require Import ectx_language language.
From iris.base_logic.lib Require Import own.
From D Require Import iris_prelude asubst_intf cmra_prop_lift
     swap_later_impl persistence.
From D Require saved_interp_n.
From D.iris_extra Require det_reduction.

Module Type LiftWp (Import VS : VlSortsSig).
  Export prelude saved_interp_n.
  Implicit Types (v : vl) (σ vs : vls) (Σ : gFunctors).
  Include SavedHoInterp VS.

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

  (** ** Instance of [irisGS] enable using the expression weakest precondition; this instance. *)
  Instance dlangG_irisG `{dlangG Σ} : irisGS dlang_lang Σ := {
    irisG_langdet := _;
  }.

  (** Notation [s ↝n φ] generalizes [s ↝ φ] on paper. *)
  Notation "s ↝n φ" := (s ⤇ φ) (at level 20) : bi_scope.

  Program Definition hoEnvD_inst {Σ} σ : hoEnvD Σ -n> hoD Σ :=
    λne φ, λ args, φ args (∞ σ).
  Next Obligation. move => Σ σ n x y Heq args. exact: Heq. Qed.

  Definition stamp_σ_to_type `{dlangG Σ} (s : gname) σ (ψ : hoD Σ) : iProp Σ :=
    ∃ φ : hoEnvD Σ, s ↝n φ ∧ ▷ (ψ ≡ hoEnvD_inst σ φ).
  Notation "s ↗n[ σ  ] ψ" := (stamp_σ_to_type s σ ψ) (at level 20) : bi_scope.

  (* Beware: to prove [sD_Typ_Abs], here we must use [∞ σ.|[ρ]], not [∞ σ >> ρ]. *)
  Definition leadsto_envD_equiv `{dlangG Σ} s σ (φ : hoEnvD Σ) : iProp Σ :=
    ∃ (φ' : hoEnvD Σ),
      ⌜φ ≡ (λ args ρ, φ' args (∞ σ.|[ρ]))⌝ ∧ s ↝n φ'.
  Arguments leadsto_envD_equiv /.
  Notation "s ↝[ σ  ] φ" := (leadsto_envD_equiv s σ φ) (at level 20).

  Section mapsto.
    Context `{Hdlang : dlangG Σ}.

    #[global] Instance stamp_σ_to_type_contractive s σ : Contractive (stamp_σ_to_type s σ).
    Proof. rewrite /stamp_σ_to_type. solve_contractive_ho. Qed.

    (* Needed for [stamp_σ_to_type_agree] if it uses [simpl]. *)
    #[local] Hint Extern 10 (IntoInternalEq (_ ≡ _) _ _) =>
      apply class_instances_internal_eq.into_internal_eq_internal_eq : typeclass_instances.

    Lemma stamp_σ_to_type_agree {σ s ψ1 ψ2} args v :
      s ↗n[ σ ] ψ1 -∗ s ↗n[ σ ] ψ2 -∗ ▷ (ψ1 args v ≡ ψ2 args v).
    Proof.
      iDestruct 1 as (φ1) "[Hsg1 Heq1]"; iDestruct 1 as (φ2) "[Hsg2 Heq2] /=".
      iDestruct (saved_ho_sem_type_agree args (∞ σ) v with "Hsg1 Hsg2") as "Heq"; iNext.
      iRewrite "Heq1"; iRewrite "Heq2". iApply "Heq".
    Qed.

    Lemma stamp_σ_to_type_intro s σ (φ : hoEnvD Σ) :
      s ↝n φ -∗ s ↗n[ σ ] hoEnvD_inst σ φ.
    Proof. rewrite /stamp_σ_to_type. iIntros; iExists φ; auto. Qed.

    #[global] Instance stamp_σ_to_type_persistent σ s ψ :
      Persistent (s ↗n[ σ ] ψ) := _.
  End mapsto.

  Typeclasses Opaque stamp_σ_to_type.
  #[global] Opaque stamp_σ_to_type.

  Module dlang_adequacy.
    Definition dlangΣ := #[savedHoSemTypeΣ].

    #[local] Instance dlangG_dlangΣ
      `{InhabitedState dlang_lang} `{!LangDet dlang_lang} : dlangG dlangΣ.
    Proof. split; apply _. Qed.

    #[local] Instance CmraSwappable_dlang : CmraSwappable (iResUR dlangΣ) := CmraSwappable_iResUR _.

    (* Enable these instances only for those who [Import] this module explicitly. *)
    #[export] Hint Resolve dlangG_dlangΣ CmraSwappable_dlang : typeclass_instances.
    Export det_reduction.
  End dlang_adequacy.
End LiftWp.
