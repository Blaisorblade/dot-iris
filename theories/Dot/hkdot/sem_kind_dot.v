From Coq Require FunctionalExtensionality.
From D Require Import iris_prelude proper proofmode_extra.
From D Require Export succ_notation.
From D Require Import saved_interp_n asubst_intf dlang lty.
From D Require Import swap_later_impl.
From D.Dot Require Import dot_lty hkdot.sem_kind.

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

Definition sem_kind_path_repl {Σ} p q (K1 K2 : sf_kind Σ) : Prop :=
  ∀ ρ T1 T2, alias_paths p.|[ρ] q.|[ρ] → K1 ρ T1 T2 ≡ K2 ρ T1 T2.
Notation "K1 ~sKd[ p := q  ]* K2" :=
  (sem_kind_path_repl p q K1 K2) (at level 70).

Definition oDTMemRaw `{!dlangG Σ} (rK : env → hoD Σ → iProp Σ): dltyO Σ := Dlty (λI ρ d,
  ∃ ψ, d ↗n ψ ∧ rK ρ ψ).

Definition oDTMemK `{!dlangG Σ} (K : sf_kind Σ) : dltyO Σ :=
  oDTMemRaw (λI ρ ψ, K ρ (packHoLtyO ψ) (packHoLtyO ψ)).

Definition oDTMemSpec `{!dlangG Σ} (L U : oltyO Σ) : dltyO Σ :=
  oDTMemK (sf_kintv L U).

(** Not a "real" kind, just a predicate over types. *)
Definition dot_intv_type_pred `{!dlangG Σ} (τ1 τ2 : oltyO Σ) ρ ψ : iProp Σ :=
  τ1 anil ρ ⊆ packHoLtyO ψ anil ∧ packHoLtyO ψ anil ⊆ τ2 anil ρ.

Section sem_TMem.
  Context `{HdotG: !dlangG Σ}.
  Implicit Types (τ : oltyO Σ).

  (** [ D⟦ { A :: τ1 .. τ2 } ⟧ ]. *)
  Definition oDTMem τ1 τ2 : dltyO Σ := oDTMemRaw (dot_intv_type_pred τ1 τ2).
  #[global] Instance oDTMem_proper : Proper ((≡) ==> (≡) ==> (≡)) oDTMem.
  Proof.
    rewrite /oDTMem => ??? ??? ??/=; properness; try reflexivity;
      solve_proper_ho.
  Qed.

  (** Define [cTMem] by lifting [oDTMem] to [clty]s. *)
  (**
  [ Ds⟦ { l :: τ1 .. τ2 } ⟧] and [ V⟦ { l :: τ1 .. τ2 } ⟧ ].
  Beware: the ICFP'20 defines instead
  [ Ds⟦ { l >: τ1 <: τ2 } ⟧] and [ V⟦ { l >: τ1 <: τ2 } ⟧ ],
  which are here a derived notation; see [cTMemL]. *)
  Definition cTMem l τ1 τ2 : clty Σ := dty2clty l (oDTMem τ1 τ2).
  #[global] Instance cTMem_proper l : Proper ((≡) ==> (≡) ==> (≡)) (cTMem l).
  Proof. solve_proper. Qed.

  Lemma cTMem_eq l τ1 τ2 d ρ :
    cTMem l τ1 τ2 ρ [(l, d)] ⊣⊢ oDTMem τ1 τ2 ρ d.
  Proof. apply dty2clty_singleton. Qed.
End sem_TMem.

Notation oTMem l τ1 τ2 := (clty_olty (cTMem l τ1 τ2)).

Section oTMem_lemmas.
  Context `{HdotG: !dlangG Σ}.

  Lemma oTMem_eq l τ1 τ2 args ρ v :
    oTMem l τ1 τ2 args ρ v ⊣⊢
    ∃ ψ d, ⌜v @ l ↘ d⌝ ∧ d ↗n ψ ∧ dot_intv_type_pred τ1 τ2 ρ ψ.
  Proof. apply bi_exist_nested_swap. Qed.

  Lemma oTMem_shift A L U : oTMem A (shift L) (shift U) = shift (oTMem A L U).
  Proof. done. Qed.
End oTMem_lemmas.

Lemma oDTMemSpec_oDTMem_eq `{!dlangG Σ} L U : oDTMemSpec L U ≡ oDTMem L U.
Proof.
  move=> ρ d /=; f_equiv=> ψ; f_equiv. apply sr_kintv_refl.
Qed.

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

  #[global] Instance oDTMemK_ne : NonExpansive (oDTMemK (Σ := Σ)).
  Proof. solve_proper_ho. Qed.
  #[global] Instance oDTMemK_proper :
    Proper ((≡) ==> (≡)) (oDTMemK (Σ := Σ)) := ne_proper _.
  #[global] Instance cTMemK_ne l : NonExpansive (cTMemK (Σ := Σ) l).
  Proof. solve_proper_ho. Qed.
  #[global] Instance cTMemK_proper l :
    Proper ((≡) ==> (≡)) (cTMemK (Σ := Σ) l) := ne_proper _.

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

  Lemma sTEq_Beta (T : oltyO Σ) p :
    oTApp (oLam T) p ≡ T .sTp[ p /].
  Proof. done. Qed.

  Lemma sTEq_BetaV (T : oltyO Σ) v :
    oTAppV (oLam T) v ≡ T.|[v/].
  Proof. move => args ρ w /=. by rewrite subst_swap_base. Qed.

End proper_eq.
End HkDotSemTypes.
