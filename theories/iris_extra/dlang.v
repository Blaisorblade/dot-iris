(** * Instantiate Iris for D* languages. *)
From iris.program_logic Require Import ectx_language language.
From D.pure_program_logic Require adequacy.
From D Require Import iris_prelude swap_later_impl asubst_intf.
From D Require gen_iheap saved_interp_dep.
From D.iris_extra Require det_reduction.

Set Suggest Proof Using.
Set Default Proof Using "Type".

Local Notation gdom g := (dom (gset stamp) g).

Module mapsto.
Export gen_iheap.
Notation sγmap := (gmap stamp gname).

Notation "s ↦ γ" := (mapsto (L := stamp) s γ) (at level 20) : bi_scope.
Notation allGs sγ := (gen_iheap_ctx (L := stamp) sγ).

Section mapsto_stamp_gname.
  Context `{gen_iheapG stamp gname Σ}.
  Global Instance stampMapsToPersist: Persistent (s ↦ γ) := _.
  Global Instance stampMapsToTimeless: Timeless (s ↦ γ) := _.
End mapsto_stamp_gname.
End mapsto.

Module Type LiftWp (Import VS : VlSortsSig).
  Export mapsto prelude saved_interp_dep.
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
    dlangG_interpNames :> gen_iheapG stamp gname Σ;
    dlangG_langdet :> LangDet dlang_lang;
  }.
  Arguments DLangG _ {_ _ _ _}.

  (** ** Instance of [irisG] enable using the expression weakest precondition; this instance. *)
  Instance dlangG_irisG `{dlangG Σ} : irisG dlang_lang Σ := {
    irisG_langdet := _;
  }.

  (** Notation [s ↝n[ n  ] φ] generalizes [s ↝ φ] on paper; [n] is the arity. *)
  Definition leadsto_n `{dlangG Σ}
    s n (φ : hoEnvD Σ n) : iProp Σ := ∃ γ, s ↦ γ ∧ γ ⤇n[ n ] φ.
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
    Proof.
      iDestruct 1 as (γ1) "[Hs1 Hg1]"; iDestruct 1 as (γ2) "[Hs2 Hg2]".
      iDestruct (mapsto_agree with "Hs1 Hs2") as %->.
      iDestruct (saved_ho_sem_type_agree_dep_abs with "Hg1 Hg2") as (->) "Hgoal".
      by iExists eq_refl.
    Qed.

    Lemma leadsto_agree_dep {s n1 n2 φ1 φ2} args ρ v :
      s ↝n[ n1 ] φ1 -∗ s ↝n[ n2 ] φ2 -∗ ∃ Heq : n1 = n2,
        ▷ ((rew [hoEnvD Σ] Heq in φ1) args ρ v ≡ φ2 args ρ v).
    Proof.
      iIntros "Hsg1 Hsg2".
      iDestruct (leadsto_agree_dep_abs with "Hsg1 Hsg2") as (->) "Hgoal".
      iExists eq_refl; cbn. iNext.
      by repeat setoid_rewrite discrete_fun_equivI.
    Qed.

    Lemma leadsto_agree {s n φ1 φ2} args ρ v :
      s ↝n[ n ] φ1 -∗ s ↝n[ n ] φ2 -∗ ▷ (φ1 args ρ v ≡ φ2 args ρ v).
    Proof.
      iIntros "Hs1 Hs2".
      iDestruct (leadsto_agree_dep args ρ v with "Hs1 Hs2") as (Heq) "Hgoal".
      by rewrite (proof_irrel Heq eq_refl) /=.
    Qed.

    Lemma leadsto_alloc {sγ s i} (φ : hoEnvD Σ i) :
      sγ !! s = None → allGs sγ ==∗
      ∃ sγ', ⌜gdom sγ' ≡ {[s]} ∪ gdom sγ⌝ ∧ allGs sγ' ∧ s ↝n[ i ] φ.
    Proof.
      iIntros (HsFresh) "Hallsγ".
      iMod (saved_ho_sem_type_alloc i φ) as (γ) "Hγ".
      iMod (gen_iheap_alloc _ _ γ HsFresh with "Hallsγ") as "[Hallsγ Hs]".
      iModIntro; iExists (<[s:=γ]> sγ); rewrite dom_insert.
      repeat iSplit; last iExists γ; by iFrame.
    Qed.

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

  Module stamp_transfer.
    Notation sγmap := (gmap stamp gname).
    Implicit Types (s: stamp) (sγ : sγmap).

    Notation freshMappings g sγ := (∀ s, s ∈ gdom g → sγ !! s = None).

    Lemma freshMappings_split (X : Type) (x : X) (g : gmap stamp X) s sγ :
      freshMappings (<[s:=x]> g) sγ → sγ !! s = None ∧ freshMappings g sγ.
    Proof.
      intros Hdom; split => [|s' Hs']; apply Hdom;
        rewrite dom_insert; set_solver.
    Qed.

    Section sem.
      Context `{Hdlang : dlangG Σ}.
      Implicit Types (gφ : gmap stamp (hoEnvD Σ 0)).

      Definition wellMappedφ gφ : iProp Σ :=
        □∀ s φ (Hl : gφ !! s = Some φ), s ↝n[ 0 ] φ.
      Global Instance wellMappedφ_persistent gφ: Persistent (wellMappedφ gφ) := _.

      Lemma wellMappedφ_empty : ⊢ wellMappedφ ∅. Proof. by iIntros (???). Qed.

      Lemma wellMappedφ_insert gφ s φ :
        wellMappedφ gφ -∗ s ↝n[ 0 ] φ -∗ wellMappedφ (<[s:=φ]> gφ).
      Proof.
        iIntros "#Hwmg #Hs !>" (s' φ' Hl). case: (decide (s' = s)) Hl => [->|?];
          rewrite (lookup_insert, lookup_insert_ne) => ?;
          simplify_eq; by [> iApply "Hs" | iApply "Hwmg"].
      Qed.

      Lemma wellMappedφ_apply s φ gφ : gφ !! s = Some φ → wellMappedφ gφ -∗ s ↝n[ 0 ] φ.
      Proof. iIntros (Hl) "#Hm"; iApply ("Hm" $! _ _ Hl). Qed.

      Lemma wellMappedφ_extend gφ1 gφ2 (Hle : gφ2 ⊆ gφ1):
          wellMappedφ gφ1 -∗ wellMappedφ gφ2.
      Proof.
        iIntros "#Hs" (s φ Hl) "/= !>". iApply ("Hs" with "[%]").
        by eapply map_subseteq_spec, Hl.
      Qed.

      Global Opaque wellMappedφ.

      Lemma transfer' {gφ} sγ : freshMappings gφ sγ → allGs sγ ==∗
        ∃ sγ', ⌜gdom sγ' ≡ gdom gφ ∪ gdom sγ⌝ ∧ allGs sγ' ∧ wellMappedφ gφ.
      Proof.
        elim gφ using map_ind.
        - iIntros "/=" (Hdom) "Hallsγ !>". iExists sγ; iFrame; iSplit.
          + by rewrite dom_empty left_id.
          + by iApply wellMappedφ_empty.
        - iIntros (s φ gφ' Hsg IH [Hssγ Hdom]%freshMappings_split) "Hown".
          iMod (IH Hdom with "Hown") as (sγ' Hsγ') "[Hallsγ #Hwmg]".
          iMod (leadsto_alloc (s := s) φ with "Hallsγ") as (sγ'' Hsγ'') "[Hgs #Hs]".
          + eapply (not_elem_of_dom (D := gset stamp)).
            by rewrite Hsγ' not_elem_of_union !not_elem_of_dom.
          + iModIntro; iExists sγ''; iFrame "Hgs"; iSplit.
            by iIntros "!%"; rewrite Hsγ'' Hsγ' dom_insert union_assoc.
            by iApply wellMappedφ_insert.
      Qed.

      Lemma transfer gφ sγ : freshMappings gφ sγ → allGs sγ ==∗ wellMappedφ gφ.
      Proof.
        iIntros (Hs) "H". by iMod (transfer' sγ Hs with "H") as (sγ' _) "[_ $]".
      Qed.

      Lemma transfer_empty gφ : allGs ∅ ==∗ wellMappedφ gφ.
      Proof. exact: transfer. Qed.
    End sem.
  End stamp_transfer.

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
      apply Swappable_iResUR; rewrite /gid /=.
      do 2 (apply fin_S_inv; cbn; first apply _).
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
      (Hwp : ∀ (Hdlang : dlangG Σ) `(!SwapPropI Σ), allGs ∅ ==∗ WP e {{ v, Φ Hdlang v }}) :
      adequate e (λ v, Ψ v).
    Proof.
      apply (wp_adequacy (Σ := Σ) (Λ := dlang_lang) e Ψ) => /=.
      iMod (gen_iheap_init (L := stamp) ∅) as (hG) "Hgs".
      set (DLangΣ := DLangG Σ).
      iMod (Hwp DLangΣ with "Hgs") as "Hwp".
      iIntros "!>".
      iApply (wp_wand with "Hwp"). by iIntros (v); iApply Himpl.
    Qed.

    Corollary safety_dlang Σ `{dlangPreG Σ} `{SwapPropI Σ}
      (Φ : dlangG Σ → val dlang_lang → iProp Σ) e
      (Hwp : ∀ (Hdlang : dlangG Σ) `(!SwapPropI Σ),
        allGs ∅ ==∗ WP e {{ Φ Hdlang }}):
      safe e.
    Proof. apply adequate_safe, (adequacy_dlang Σ e Φ), Hwp; naive_solver. Qed.
    End LangDet.
  End dlang_adequacy.

  (* Backward compatibility. *)
  Notation "s ↝ φ" := (s ↝n[ 0 ] vopen φ)%I  (at level 20) : bi_scope.
  Notation "s ↗[ σ  ] ψ" := (s ↗n[ σ , 0 ] vopen ψ)%I (at level 20) : bi_scope.
End LiftWp.
