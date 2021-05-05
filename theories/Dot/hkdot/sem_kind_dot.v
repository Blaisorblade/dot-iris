From Coq Require FunctionalExtensionality.
From D Require Import iris_prelude proper proofmode_extra.
From D Require Export succ_notation.
From D Require Import saved_interp_n asubst_intf dlang lty.
From D Require Import swap_later_impl.
From D.Dot Require Import dot_lty hkdot.sem_kind path_wp.

Set Suggest Proof Using.
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (Σ : gFunctors).

Module Export HkDotSemTypes.
Include HoSemTypes VlSorts dlang_inst dot_lty.

Implicit Types
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : var → vl) (l : label).

(** * Type members. *)

(** When a definition points to a semantic type. Inlined in paper. *)
Definition dm_to_type `{HdotG: !dlangG Σ} d (ψ : hoD Σ) : iProp Σ :=
  ∃ s σ, ⌜ d = dtysem σ s ⌝ ∧ s ↗n[ σ ] ψ.
Notation "d ↗n ψ" := (dm_to_type d ψ) (at level 20).
Notation "d ↗ ψ" := (dm_to_type d ψ) (at level 20).

Section dm_to_type.
  Context `{HdotG: !dlangG Σ}.

  Lemma dm_to_type_agree {d ψ1 ψ2} args v : d ↗n ψ1 -∗ d ↗n ψ2 -∗ ▷ (ψ1 args v ≡ ψ2 args v).
  Proof.
    iDestruct 1 as (s σ ?) "#Hs1".
    iDestruct 1 as (s' σ' ?) "#Hs2".
    simplify_eq. by iApply (stamp_σ_to_type_agree args with "Hs1 Hs2").
  Qed.

  Lemma dm_to_type_intro d s σ φ :
    d = dtysem σ s → s ↝n φ -∗ d ↗n hoEnvD_inst σ φ.
  Proof.
    iIntros. iExists s, σ. iFrame "%".
    by iApply stamp_σ_to_type_intro.
  Qed.

  #[global] Opaque dm_to_type.
End dm_to_type.

Definition sem_kind_path_repl {Σ} p q (K1 K2 : sf_kind Σ) : Prop :=
  ∀ ρ T1 T2, alias_paths p.|[ρ] q.|[ρ] → K1 ρ T1 T2 ≡ K2 ρ T1 T2.
Notation "K1 ~sKd[ p := q  ]* K2" :=
  (sem_kind_path_repl p q K1 K2) (at level 70).

(* TODO inline. *)
Definition oDTMemRaw `{!dlangG Σ} (rK : env → hoD Σ → iProp Σ): dltyO Σ := Dlty (λI ρ d,
  ∃ ψ, d ↗n ψ ∧ rK ρ ψ).

(** [ D⟦ { A :: K } ⟧ ]. *)
Definition oDTMemK `{!dlangG Σ} (K : sf_kind Σ) : dltyO Σ :=
  oDTMemRaw (λI ρ ψ, K ρ (packHoLtyO ψ) (packHoLtyO ψ)).

(** [ D⟦ { A :: τ1 .. τ2 } ⟧ ]. *)
Definition oDTMem `{!dlangG Σ} (L U : oltyO Σ) : dltyO Σ :=
  oDTMemK (sf_kintv L U).

Section oDTMem.
  Context `{!dlangG Σ}.

  (** Not a "real" kind, just a predicate over types. *)
  Definition dot_intv_type_pred τ1 τ2 ρ ψ : iProp Σ :=
    τ1 anil ρ ⊆ packHoLtyO ψ anil ∧ packHoLtyO ψ anil ⊆ τ2 anil ρ.

  (* Definition oDTMem_unfold L U : dltyO Σ := oDTMemRaw (dot_intv_type_pred L U). *)

  (* oDTMem_unfold L U. *)
  Lemma oDTMem_unfold L U : oDTMem L U ≡ oDTMemRaw (dot_intv_type_pred L U).
  Proof. move=> ρ d /=; f_equiv=> ψ; f_equiv. apply sr_kintv_refl. Qed.
End oDTMem.

Definition cTMemK `{!dlangG Σ} l (K : sf_kind Σ) : clty Σ := dty2clty l (oDTMemK K).
Notation oTMemK l K := (clty_olty (cTMemK l K)).

Definition oDTMemAnyKind `{!dlangG Σ} : dltyO Σ := Dlty (λI ρ d,
  ∃ (ψ : hoD Σ), d ↗n ψ).
Definition cTMemAnyKind `{!dlangG Σ} l : clty Σ := dty2clty l oDTMemAnyKind.
Notation oTMemAnyKind l := (clty_olty (cTMemAnyKind l)).

Program Definition kpSubstOne `{!dlangG Σ} p (K : sf_kind Σ) : sf_kind Σ :=
  SfKind
    (λI ρ T1 T2, path_wp p.|[ρ] (λ v, K (v .: ρ) T1 T2)).
Next Obligation.
  move=> Σ ? p K v m T1 T2 HT U1 U2 HU /=. f_equiv=>?. exact: sf_kind_sub_ne_2.
Qed.
Next Obligation.
  iIntros "* #Heq1 #Heq2 H". iApply (path_wp_wand with "H");
    iIntros "* HK"; iApply (sf_kind_sub_internal_proper with "Heq1 Heq2 HK").
Qed.
Next Obligation.
  iIntros "* HK1 HK2". iDestruct (path_wp_and' with "HK1 HK2") as "HK".
  iApply (path_wp_wand with "HK"); iIntros "* [HK1 HK2]".
  iApply (sf_kind_sub_trans with "HK1 HK2").
Qed.
Next Obligation.
  iIntros "* H"; iApply (path_wp_wand with "H"); iIntros "*".
  iApply sf_kind_sub_quasi_refl_1.
Qed.
Next Obligation.
  iIntros "* H"; iApply (path_wp_wand with "H"); iIntros "*".
  iApply sf_kind_sub_quasi_refl_2.
Qed.
Notation "K .sKp[ p /]" := (kpSubstOne p K) (at level 65).

Definition oTApp `{!dlangG Σ} (T : oltyO Σ) (p : path) : oltyO Σ :=
  Olty (λ args ρ v, path_wp p.|[ρ] (λ w, T (acons w args) ρ v)).

Section proper_eq.
  Context `{!dlangG Σ}.

  #[global] Instance oDTMemRaw_ne n :
    Proper (pointwise_relation _ ((dist n) ==> (dist n)) ==> (dist n)) oDTMemRaw.
  Proof.
    rewrite /oDTMemRaw => rK1 rK2 HrK ρ d /=; repeat f_equiv.
    exact: HrK.
  Qed.

  #[global] Instance oDTMemRaw_proper :
    Proper (pointwise_relation _ ((≡) ==> (≡)) ==> (≡)) oDTMemRaw.
  Proof.
    rewrite /oDTMemRaw => rK1 rK2 HrK ρ d /=.
    properness; [done|]. exact: HrK.
  Qed.

  #[global] Instance oDTMemK_ne : NonExpansive (oDTMemK (Σ := Σ)).
  Proof. solve_proper_ho. Qed.
  #[global] Instance oDTMemK_proper :
    Proper ((≡) ==> (≡)) (oDTMemK (Σ := Σ)) := ne_proper _.

  #[global] Instance cTMemK_ne l : NonExpansive (cTMemK (Σ := Σ) l).
  Proof. solve_proper_ho. Qed.
  #[global] Instance cTMemK_proper l :
    Proper ((≡) ==> (≡)) (cTMemK (Σ := Σ) l) := ne_proper _.

  #[global] Instance oDTMem_proper : Proper ((≡) ==> (≡) ==> (≡)) oDTMem.
  Proof. rewrite /oDTMem=>??? ???. by repeat f_equiv. Qed.

  Lemma cTMemK_eq l (K : sf_kind Σ) d ρ :
    cTMemK l K ρ [(l, d)] ⊣⊢ oDTMemK K ρ d.
  Proof. apply dty2clty_singleton. Qed.

  Lemma oTMemK_eq l K args ρ v :
    oTMemK l K args ρ v ⊣⊢
    ∃ ψ d, ⌜v @ l ↘ d⌝ ∧ d ↗n ψ ∧ K ρ (packHoLtyO ψ) (packHoLtyO ψ).
  Proof. apply bi_exist_nested_swap. Qed.

  Lemma cTMemAnyKind_eq l d ρ :
    cTMemAnyKind l ρ [(l, d)] ⊣⊢ oDTMemAnyKind ρ d.
  Proof. apply dty2clty_singleton. Qed.

  Lemma cTMemK_subst l (K : sf_kind Σ) ρ :
    (oTMemK l K).|[ρ] = oTMemK l K.|[ρ].
  Proof. done. Qed.

  Lemma kpSubstOne_eq (K : sf_kind Σ) v :
    K.|[v/] ≡ K .sKp[ pv v /].
  Proof. move=> ???. by rewrite /= path_wp_pv_eq subst_swap_base. Qed.

  Lemma oTApp_pv (T : oltyO Σ) w :
    oTApp T (pv w) ≡ oTAppV T w.
  Proof. intros ???. by rewrite /= path_wp_pv_eq. Qed.

  Lemma sTEq_oLaterN_oTApp_pv (τ : oltyO Σ) m v:
    oLaterN m (oTApp τ (pv v)) ≡ oTApp (oLaterN m τ) (pv v).
  Proof. by rewrite !oTApp_pv. Qed.

  Lemma sTSub_oTApp_oLaterN (τ : oltyO Σ) m p args ρ v:
    oTApp (oLaterN m τ) p args ρ v ⊢ oLaterN m (oTApp τ p) args ρ v.
  Proof. by rewrite /= path_wp_laterN_swap. Qed.

  (* XXX why here? *)
  Lemma sTEq_Beta (T : oltyO Σ) p :
    oTApp (oLam T) p ≡ T .sTp[ p /].
  Proof. done. Qed.

  Lemma sTEq_BetaV (T : oltyO Σ) v :
    oTAppV (oLam T) v ≡ T.|[v/].
  Proof. move => args ρ w /=. by rewrite subst_swap_base. Qed.

End proper_eq.

Typeclasses Opaque oDTMem.
#[global] Opaque oDTMem.

End HkDotSemTypes.
