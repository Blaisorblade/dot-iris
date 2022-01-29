(** * Semantic lemmas for double-delay subtyping. *)
From iris.proofmode Require Import proofmode.

From D Require Import iris_prelude swap_later_impl.
From D.Dot Require Import rules path_repl dot_semtypes dsub_lr defs_lr binding_lr.

Implicit Types (Σ : gFunctors)
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : env) (l : label).

Notation sstpi' i j Γ τ1 τ2 :=
  (∀ ρ v,
    sG⟦Γ⟧*ρ → ▷^i oClose τ1 ρ v → ▷^j oClose τ2 ρ v)%I.

Section defs.
  Context {Σ}.
  Implicit Types (τ : oltyO Σ).

  (** Legacy: (double)-indexed subtyping. *)
  Definition sstpi `{!dlangG Σ} i j Γ τ1 τ2 : iProp Σ :=
    |==> sstpi' i j Γ τ1 τ2.
  #[global] Arguments sstpi /.
End defs.
(** Indexed subtyping *)
Notation "Γ s⊨ T1 , i <: T2 , j" := (sstpi i j Γ T1 T2) (at level 74, T1, T2, i, j at next level).

(** * Proper instances. *)
Section Propers.
  Context `{HdotG : !dlangG Σ}.
  Implicit Types (τ L T U : olty Σ).

  #[global] Instance sstpi_proper i j : Proper3 (sstpi i j).
  Proof.
    solve_proper_ho.
    (* intros ?? HG ?? H1 ?? H2; simplify_eq/=.
    properness; [by rewrite HG|apply H1|apply H2]. *)
  Qed.
  #[global] Instance : Params (@sstpi) 4 := {}.
End Propers.

Section judgment_lemmas.
  Context `{!dlangG Σ}.

  Lemma sstpi_app ρ Γ (T1 T2 : olty Σ) i j :
    sstpi' i j Γ T1 T2 -∗ sG⟦ Γ ⟧* ρ -∗
    oClose (oLaterN i T1) ρ ⊆ oClose (oLaterN j T2) ρ.
  Proof. iIntros "Hsub Hg %v"; iApply ("Hsub" with "Hg"). Qed.

  Lemma sstpd0_to_sstpi0 Γ T1 T2 :
    Γ s⊨ T1 <:[0] T2 ⊣⊢
    Γ s⊨ T1, 0 <: T2, 0.
  Proof. by rewrite /sstpi sstpd_eq. Qed.

  Lemma sstpi_to_sstpd0 Γ i j T1 T2 :
    Γ s⊨ T1, i <: T2, j ⊣⊢
    Γ s⊨ oLaterN i T1 <:[0] oLaterN j T2.
  Proof. by rewrite sstpd0_to_sstpi0. Qed.

  Lemma sstpd_to_sstpi Γ i T1 T2 `{!SwapPropI Σ} :
    Γ s⊨ T1 <:[i] T2 ⊣⊢
    Γ s⊨ T1, i <: T2, i.
  Proof. by rewrite /sstpi -sstpd_delay_oLaterN sstpd_eq. Qed.
End judgment_lemmas.

Section StpLemmas.
  Context `{HdotG : !dlangG Σ}.

  Lemma sP_ISub {Γ p T1 T2 i j} :
    Γ s⊨p p : T1, i -∗
    Γ s⊨ T1, i <: T2, i + j -∗
    (*───────────────────────────────*)
    Γ s⊨p p : T2, i + j.
  Proof.
    iIntros ">#HpT1 >#Hsub !> %ρ #Hg".
    iSpecialize ("HpT1" with "Hg").
    rewrite !path_wp_eq.
    iDestruct "HpT1" as (v) "Hpv"; iExists v.
    iDestruct "Hpv" as "-#[$ #HpT1]". by iApply "Hsub".
  Qed.

  Lemma sT_ISub {Γ e T1 T2 i} :
    Γ s⊨ e : T1 -∗
    Γ s⊨ T1, 0 <: T2, i -∗
    (*───────────────────────────────*)
    Γ s⊨ iterate tskip i e : T2.
  Proof.
    rewrite sstpi_to_sstpd0 oLaterN_0; iIntros "He Hsub".
    iApply sT_SkipN.
    iApply (sT_Sub with "He Hsub").
  Qed.
End StpLemmas.
