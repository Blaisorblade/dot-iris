From Coq Require FunctionalExtensionality.
From D Require Import iris_prelude proper proofmode_extra.
From D Require Export succ_notation.
From D Require Import saved_interp_n asubst_intf dlang lty.
From D Require Import swap_later_impl.
From D.Dot Require Import dot_lty hkdot.sem_kind.

Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (Σ : gFunctors).

Module Export HkDotSemTypes.
Include HoSemTypes VlSorts dlang_inst dot_lty.

Implicit Types
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : var → vl) (l : label).

(** * Type members *)
Notation oDTMemRaw rK := (Dlty (λI ρ d, ∃ ψ, d ↗ ψ ∧ rK ρ ψ)).

(** [ D⟦ { A :: K } ⟧ ]. *)
Definition oDTMemK `{!dlangG Σ} `[!RecTyInterp Σ] (K : sf_kind Σ) : dltyO Σ :=
  oDTMemRaw (λI ρ ψ, K ρ (packHoLtyO ψ) (packHoLtyO ψ)).
#[global] Instance : Params (@oDTMemK) 2 := {}.

Definition cTMemK `{!dlangG Σ} l `[!RecTyInterp Σ] (K : sf_kind Σ) : clty Σ := dty2clty l (oDTMemK K).
#[global] Instance : Params (@cTMemK) 3 := {}.
Notation oTMemK l K := (clty_olty (cTMemK l K)).

Definition oDTMemAnyKind `{!dlangG Σ} `{!RecTyInterp Σ} : dltyO Σ := Dlty (λI ρ d,
  ∃ (ψ : hoD Σ), d ↗ ψ).
Definition cTMemAnyKind `{!dlangG Σ} l `{!RecTyInterp Σ} : clty Σ := dty2clty l oDTMemAnyKind.
Notation oTMemAnyKind l := (clty_olty (cTMemAnyKind l)).

Section TMem_Proper.
  Context `{HdotG : !dlangG Σ}.

  #[global] Instance oDTMemK_contractive n :
    Proper (dist_later n ==> dist n ==> dist n) (oDTMemK (Σ := Σ)).
  Proof. solve_contractive_ho. Qed.
  (* Both contractive and nonexpansive, since [contractive_ne_2] is not an
  instance. *)
  #[global] Instance oDTMemK_ne : NonExpansive2 (oDTMemK (Σ := Σ)) :=
    contractive_ne_R _.
  #[global] Instance oDTMemK_proper : Proper2 (oDTMemK (Σ := Σ)) :=
    ne_proper_2 _.

  #[global] Instance cTMemK_contractive l n :
    Proper (dist_later n ==> dist n ==> dist n) (cTMemK (Σ := Σ) l).
  Proof. solve_contractive_ho. Qed.
  (* Both contractive and nonexpansive, since [contractive_ne_2] is not an
  instance. *)
  #[global] Instance cTMemK_ne l : NonExpansive2 (cTMemK (Σ := Σ) l) :=
    contractive_ne_R _.
  #[global] Instance cTMemK_proper l : Proper2 (cTMemK (Σ := Σ) l) :=
    ne_proper_2 _.
End TMem_Proper.

Section TMem_lemmas.
  Context `{HdotG : !dlangG Σ} `{!RecTyInterp Σ}.

  Lemma cTMemK_eq l (K : sf_kind Σ) d ρ :
    cTMemK l K ρ [(l, d)] ⊣⊢ oDTMemK K ρ d.
  Proof. apply dty2clty_singleton. Qed.

  Lemma oTMemK_eq l K args ρ v :
    oTMemK l K args ρ v ⊣⊢
    ∃ ψ d, ⌜v ,, l ↘ d⌝ ∧ d ↗ ψ ∧ K ρ (packHoLtyO ψ) (packHoLtyO ψ).
  Proof. by rewrite /cTMemK/= bi_exist_nested_swap. Qed.

  Lemma cTMemAnyKind_eq l d ρ :
    cTMemAnyKind l ρ [(l, d)] ⊣⊢ oDTMemAnyKind ρ d.
  Proof. apply dty2clty_singleton. Qed.

  Lemma cTMemK_subst l (K : sf_kind Σ) ρ :
    (oTMemK l K).|[ρ] = oTMemK l K.|[ρ].
  Proof. done. Qed.
End TMem_lemmas.

(** ** Type members: derive special case for gDOT. *)
(** Not a "real" kind, just a predicate over types. *)
Definition dot_intv_type_pred `{!dlangG Σ} (L U : oltyO Σ) ρ ψ : iProp Σ :=
  □(L anil ρ ⊆ packHoLtyO ψ anil ∧ packHoLtyO ψ anil ⊆ U anil ρ).
#[global] Instance : Params (@dot_intv_type_pred) 2 := {}.

(** [ D⟦ { A :: τ1 .. τ2 } ⟧ ]. *)
Definition oDTMem `{!dlangG Σ} `[!RecTyInterp Σ] L U : dltyO Σ := oDTMemK (sf_kintv L U).
Definition oDTMem_eq `{!dlangG Σ} `{!RecTyInterp Σ} L U : oDTMem L U = oDTMemK (sf_kintv L U) := reflexivity _.
#[global] Instance : Params (@oDTMem) 2 := {}.

#[global] Arguments oDTMem {Σ _ _} L U ρ : rename.

Definition cTMem `{!dlangG Σ} l `[!RecTyInterp Σ] L U : clty Σ := dty2clty l (oDTMem L U).
#[global] Instance : Params (@cTMem) 3 := {}.

Notation oTMem l L U := (clty_olty (cTMem l L U)).

Section TMem_Proper.
  Context `{HdotG : !dlangG Σ}.

  #[global] Instance oDTMem_contractive n :
    Proper (dist_later n ==> dist n ==> dist n ==> dist n) (@oDTMem Σ HdotG).
  Proof. solve_contractive_ho. Qed.

  (* Not an instance: it'd break [solve_contractive] in [cTMem_contractive]. *)
  Definition oDTMem_ne : NonExpansive3 (@oDTMem Σ HdotG) :=
    contractive_ne_R _.

  #[global] Instance oDTMem_proper : Proper3 (@oDTMem Σ HdotG).
  Proof. apply ne_proper_3, oDTMem_ne. Qed.

  #[global] Instance cTMem_contractive n l : Proper (dist_later n ==> dist n ==> dist n ==> dist n) (cTMem l).
  Proof. solve_contractive. Qed.

  Definition cTMem_ne l : NonExpansive3 (cTMem l) :=
    contractive_ne_R _.
  #[global] Instance cTMem_proper l : Proper3 (cTMem l).
  Proof. apply ne_proper_3, cTMem_ne. Qed.
End TMem_Proper.

Section sem_TMem.
  Context `{HdotG : !dlangG Σ} `{!RecTyInterp Σ}.
  Implicit Types (τ : oltyO Σ).

  Lemma oDTMem_unfold L U : oDTMem L U ≡ oDTMemRaw (dot_intv_type_pred L U).
  Proof.
    rewrite oDTMem_eq => ρ d /=. f_equiv=> ψ; f_equiv. apply sr_kintv_refl.
  Qed.

  (** Define [cTMem] by lifting [oDTMem] to [clty]s. *)
  (**
  [ Ds⟦ { l :: τ1 .. τ2 } ⟧] and [ V⟦ { l :: τ1 .. τ2 } ⟧ ].
  Beware: the ICFP'20 defines instead
  [ Ds⟦ { l >: τ1 <: τ2 } ⟧] and [ V⟦ { l >: τ1 <: τ2 } ⟧ ],
  which are here a derived notation; see [cTMemL]. *)

  Lemma cTMem_unfold l L U :
    cTMem l L U ≡ dty2clty l (oDTMemRaw (dot_intv_type_pred L U)).
  Proof. by rewrite /cTMem oDTMem_unfold. Qed.

  Lemma cTMem_eq l L U d ρ :
    cTMem l L U ρ [(l, d)] ⊣⊢ oDTMem L U ρ d.
  Proof. apply dty2clty_singleton. Qed.

  Lemma oTMem_unfold l L U :
    oTMem l L U ≡ clty_olty (dty2clty l (oDTMemRaw (dot_intv_type_pred L U))).
  Proof. by rewrite cTMem_unfold. Qed.

  Lemma oTMem_eq l L U args ρ v :
    oTMem l L U args ρ v ⊣⊢
    ∃ ψ d, ⌜v ,, l ↘ d⌝ ∧ d ↗ ψ ∧ dot_intv_type_pred L U ρ ψ.
  Proof. rewrite oTMem_unfold. apply bi_exist_nested_swap. Qed.

  Lemma oTMem_shift A L U : oTMem A (shift L) (shift U) = shift (oTMem A L U).
  Proof. rewrite /cTMem !oDTMem_eq. done. Qed.
End sem_TMem.

(** * Path application and substitution *)

Definition sem_kind_path_replI {Σ} p q (K1 K2 : sf_kind Σ) : iProp Σ :=
  <PB> ∀ ρ T1 T2 (Hal : alias_paths p.|[ρ] q.|[ρ]), K1 ρ T1 T2 ≡ K2 ρ T1 T2.
(* sKdI = semantic Kind Path Iris; matches [sem_ty_path_replI]. *)
Notation "K1 ~sKpI[ p := q  ]* K2" :=
  (sem_kind_path_replI p q K1 K2) (at level 70).

Definition sem_kind_path_repl {Σ} p q (K1 K2 : sf_kind Σ) : Prop :=
  ∀ ρ T1 T2, alias_paths p.|[ρ] q.|[ρ] → K1 ρ T1 T2 ≡ K2 ρ T1 T2.
(* sKpP = semantic Kind Path Prop; matches [sem_ty_path_repl]. *)
Notation "K1 ~sKpP[ p := q  ]* K2" :=
  (sem_kind_path_repl p q K1 K2) (at level 70).

(* Arguments are ordered to optimize setoid rewriting and maximize [Params]. *)
Definition _oTApp `{!dlangG Σ} (p : path) (T : oltyO Σ) : oltyO Σ :=
  Olty (λ args ρ v, path_wp p.|[ρ] (λ w, T (acons w args) ρ v)).
#[global] Instance : Params (@_oTApp) 3 := {}.

(* Show a more natural ordering to the user. *)
Notation oTApp T p := (_oTApp p T).

Program Definition kpSubstOne {Σ} p (K : sf_kind Σ) : sf_kind Σ :=
  SfKind
    (λI ρ T1 T2, path_wp p.|[ρ] (λ v, K (v .: ρ) T1 T2)).
Next Obligation.
  move=> Σ p K v m T1 T2 HT U1 U2 HU /=. f_equiv=>?. exact: sf_kind_sub_ne_2.
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

  #[global] Instance _oTApp_ne p : NonExpansive (_oTApp p).
  Proof. move=> n T1 T2 HT args ρ v /=. apply: path_wp_ne=> w. exact: HT. Qed.

  #[global] Instance _oTApp_proper p : Proper1 (_oTApp p) :=
    ne_proper _.

  Lemma kpSubstOne_eq (K : sf_kind Σ) v :
    K.|[v/] ≡ K .sKp[ pv v /].
  Proof. move=> ???. by rewrite /= path_wp_pv_eq subst_swap_base. Qed.

  Lemma sem_kind_path_repl_eq {p q} {K1 K2 : sf_kind Σ} :
    K1 ~sKpP[ p := q ]* K2 → ⊢ K1 ~sKpI[ p := q ]* K2.
  Proof. iIntros "%Heq !% /=". apply: Heq. Qed.

  Lemma oTApp_pv (T : oltyO Σ) w :
    oTApp T (pv w) ≡ oTAppV T w.
  Proof. intros ???. by rewrite /= path_wp_pv_eq. Qed.

  Lemma sTEq_oLaterN_oTApp_pv (τ : oltyO Σ) m v :
    oLaterN m (oTApp τ (pv v)) ≡ oTApp (oLaterN m τ) (pv v).
  Proof. by rewrite !oTApp_pv. Qed.

  Lemma sTSub_oTApp_oLaterN (τ : oltyO Σ) m p args ρ v :
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
