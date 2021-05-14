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

(** * Type members *)
Notation oDTMemRaw rK := (Dlty (λI ρ d, ∃ ψ, d ↗n ψ ∧ rK ρ ψ)).

(** [ D⟦ { A :: K } ⟧ ]. *)
Definition oDTMemK `{!dlangG Σ} (K : sf_kind Σ) : dltyO Σ :=
  oDTMemRaw (λI ρ ψ, K ρ (packHoLtyO ψ) (packHoLtyO ψ)).

Definition oDTMemSpec `{!dlangG Σ} (L U : oltyO Σ) : dltyO Σ :=
  oDTMemK (sf_kintv L U).

Definition cTMemK `{!dlangG Σ} l (K : sf_kind Σ) : clty Σ := dty2clty l (oDTMemK K).
Notation oTMemK l K := (clty_olty (cTMemK l K)).

Definition oDTMemAnyKind `{!dlangG Σ} : dltyO Σ := Dlty (λI ρ d,
  ∃ (ψ : hoD Σ), d ↗n ψ).
Definition cTMemAnyKind `{!dlangG Σ} l : clty Σ := dty2clty l oDTMemAnyKind.
Notation oTMemAnyKind l := (clty_olty (cTMemAnyKind l)).

Section TMem_Proper.
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
End TMem_Proper.

(** ** Type members: derive special case for gDOT. *)
(** Not a "real" kind, just a predicate over types. *)
Definition dot_intv_type_pred `{!dlangG Σ} (L U : oltyO Σ) ρ ψ : iProp Σ :=
  L anil ρ ⊆ packHoLtyO ψ anil ∧ packHoLtyO ψ anil ⊆ U anil ρ.

(** [ D⟦ { A :: τ1 .. τ2 } ⟧ ]. *)
Definition oDTMem_def `{!dlangG Σ} L U : dltyO Σ := oDTMemRaw (dot_intv_type_pred L U).
Definition oDTMem_aux : seal (@oDTMem_def). Proof. by eexists. Qed.
Definition oDTMem := oDTMem_aux.(unseal).
Definition oDTMem_eq : oDTMem = _ := oDTMem_aux.(seal_eq).

#[global] Arguments oDTMem {_ _} _ _  _ : assert.
Typeclasses Opaque oDTMem.
#[global] Opaque oDTMem.

Section sem_TMem.
  Context `{HdotG: !dlangG Σ}.
  Implicit Types (τ : oltyO Σ).

  Lemma oDTMem_unfold L U : oDTMem L U ≡ oDTMemRaw (dot_intv_type_pred L U).
  Proof. by rewrite oDTMem_eq. Qed.

  #[global] Instance oDTMem_proper : Proper ((≡) ==> (≡) ==> (≡)) oDTMem.
  Proof.
    move=> ??? ??? ??/=. rewrite !oDTMem_unfold/=.
    properness; try reflexivity; solve_proper_ho.
  Qed.

  (** Define [cTMem] by lifting [oDTMem] to [clty]s. *)
  (**
  [ Ds⟦ { l :: τ1 .. τ2 } ⟧] and [ V⟦ { l :: τ1 .. τ2 } ⟧ ].
  Beware: the ICFP'20 defines instead
  [ Ds⟦ { l >: τ1 <: τ2 } ⟧] and [ V⟦ { l >: τ1 <: τ2 } ⟧ ],
  which are here a derived notation; see [cTMemL]. *)
  Definition cTMem l L U : clty Σ := dty2clty l (oDTMem L U).
  #[global] Instance cTMem_proper l : Proper ((≡) ==> (≡) ==> (≡)) (cTMem l).
  Proof. solve_proper. Qed.

  Lemma cTMem_unfold l L U :
    cTMem l L U ≡ dty2clty l (oDTMemRaw (dot_intv_type_pred L U)).
  Proof. by rewrite /cTMem oDTMem_unfold. Qed.

  Lemma cTMem_eq l L U d ρ :
    cTMem l L U ρ [(l, d)] ⊣⊢ oDTMem L U ρ d.
  Proof. apply dty2clty_singleton. Qed.
End sem_TMem.

Notation oTMem l L U := (clty_olty (cTMem l L U)).

Section oTMem_lemmas.
  Context `{HdotG: !dlangG Σ}.

  Lemma oTMem_unfold l L U :
    oTMem l L U ≡ clty_olty (dty2clty l (oDTMemRaw (dot_intv_type_pred L U))).
  Proof. by rewrite cTMem_unfold. Qed.

  Lemma oTMem_eq l L U args ρ v :
    oTMem l L U args ρ v ⊣⊢
    ∃ ψ d, ⌜v @ l ↘ d⌝ ∧ d ↗n ψ ∧ dot_intv_type_pred L U ρ ψ.
  Proof. rewrite oTMem_unfold. apply bi_exist_nested_swap. Qed.

  Lemma oTMem_shift A L U : oTMem A (shift L) (shift U) = shift (oTMem A L U).
  Proof. rewrite /cTMem !oDTMem_eq. done. Qed.
End oTMem_lemmas.

Lemma oDTMemSpec_oDTMem_eq `{!dlangG Σ} L U : oDTMemSpec L U ≡ oDTMem L U.
Proof.
  rewrite oDTMem_unfold => ρ d /=; f_equiv=> ψ; f_equiv. apply sr_kintv_refl.
Qed.

(** * Path application and substitution *)

Definition sem_kind_path_repl {Σ} p q (K1 K2 : sf_kind Σ) : Prop :=
  ∀ ρ T1 T2, alias_paths p.|[ρ] q.|[ρ] → K1 ρ T1 T2 ≡ K2 ρ T1 T2.
Notation "K1 ~sKd[ p := q  ]* K2" :=
  (sem_kind_path_repl p q K1 K2) (at level 70).

Definition oTApp `{!dlangG Σ} (T : oltyO Σ) (p : path) : oltyO Σ :=
  Olty (λ args ρ v, path_wp p.|[ρ] (λ w, T (acons w args) ρ v)).

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

Section proper_eq.
  Context `{!dlangG Σ}.

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
