(** * Unstamped semantic judgments, adequacy, and typing lemmas. *)
From D Require Export iris_prelude swap_later_impl.
From D.pure_program_logic Require Import weakestpre.
From D Require Import iris_extra.det_reduction.
From D.Dot Require Import skeleton path_repl typing_aux_defs.
From D.Dot Require Import unary_lr.
From D.Dot Require Import later_sub_sem binding_lr path_repl_lr defs_lr dsub_lr prims_lr.
From stdpp Require Import relations.
(* Fix scope. *)
Import dlang_adequacy D.prelude stdpp.relations stdpp.tactics.

Implicit Types (Σ : gFunctors)
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : env) (l : label).

(* XXX *)
Arguments bupd {_}%type_scope {_} _%bi_scope.
Notation "|==> Q" := (bupd Q) : bi_scope.

Section unstamped_judgs.
  Context `{!dlangG Σ}.

  (* Semantic, Unstamped, Expression TyPing *)
  Definition suetp e_u Γ T : iProp Σ :=
    □ |==> ∃ e_s, ⌜ same_skel_tm e_u e_s⌝ ∧ Γ s⊨ e_s : T.

  Definition sudstp ds_u Γ T : iProp Σ :=
    □ |==> ∃ ds_s, ⌜ same_skel_dms ds_u ds_s⌝ ∧ Γ s⊨ds ds_s : T.

  Definition sudtp l d_u Γ T : iProp Σ :=
    □ |==> ∃ d_s, ⌜ same_skel_dm d_u d_s⌝ ∧ Γ s⊨ { l := d_s } : T.

  Definition iudtp  Γ T l d     := sudtp l d  V⟦Γ⟧* C⟦T⟧.
  Definition iudstp Γ T ds      := sudstp ds  V⟦Γ⟧* C⟦T⟧.
  Definition iuetp  Γ T e       := suetp e    V⟦Γ⟧* V⟦T⟧.
End unstamped_judgs.

Global Instance: Params (@suetp) 3 := {}.
Global Instance: Params (@sudstp) 3 := {}.
Global Instance: Params (@sudtp) 4 := {}.

Section unstamped_judgs_proper.
  Context `{!dlangG Σ}.

  Global Instance suetp_proper e : Proper ((≡) ==> (≡) ==> (≡)) (suetp e).
  Proof. rewrite /suetp => ??????. by repeat f_equiv. Qed.
  Global Instance suetp_flip_proper e :
    Proper (flip (≡) ==> flip (≡) ==> flip (≡)) (suetp e).
  Proof. apply: flip_proper_3. Qed.

  Global Instance sudstp_proper ds : Proper ((≡) ==> (≡) ==> (≡)) (sudstp ds).
  Proof. rewrite /sudstp => ??????; by repeat f_equiv. Qed.
  Global Instance sudstp_flip_proper ds :
    Proper (flip (≡) ==> flip (≡) ==> flip (≡)) (sudstp ds).
  Proof. apply: flip_proper_3. Qed.

  Global Instance sudtp_proper l d : Proper ((≡) ==> (≡) ==> (≡)) (sudtp l d).
  Proof. rewrite /sudtp => ??????. by repeat f_equiv. Qed.
  Global Instance sudtp_flip_proper l d :
    Proper (flip (≡) ==> flip (≡) ==> flip (≡)) (sudtp l d).
  Proof. apply: flip_proper_3. Qed.
End unstamped_judgs_proper.

Notation "Γ su⊨ e : T" := (suetp e Γ T) (at level 74, e, T at next level).
Notation "Γ su⊨ {  l := d  } : T" := (sudtp l d Γ T) (at level 64, d, l, T at next level).
Notation "Γ su⊨ds ds : T" := (sudstp ds Γ T) (at level 74, ds, T at next level).

Notation "Γ u⊨ {  l := d  } : T" := (iudtp Γ T l d) (at level 74, d, l, T at next level).
Notation "Γ u⊨ds ds : T" := (iudstp Γ T ds) (at level 74, ds, T at next level).
Notation "Γ u⊨ e : T" := (iuetp Γ T e) (at level 74, e, T at next level).

(* Adequacy *)
Theorem unstamped_s_safety_dot_sem Σ `{HdlangG: !dlangPreG Σ} `{!SwapPropI Σ}
  {e_u}
  (τ : ∀ `{!dlangG Σ}, olty Σ 0)
  (Hwp : ∀ `{!dlangG Σ} `(!SwapPropI Σ), ⊢ [] su⊨ e_u : τ):
  safe e_u.
Proof.
  intros e_u' [n Hsteps]%rtc_nsteps.
  eapply same_skel_safe_n_impl, Hsteps.
  apply (soundness (M := iResUR Σ) _ n).
  apply (bupd_plain_soundness _).
  (* XXX [hG] is needed, till I fix everything and drop the second map. *)
  iMod (gen_iheap_init (L := stamp) ∅) as (hG) "_".
  set (DLangΣ := DLangG Σ).
  iDestruct (Hwp DLangΣ SwapPropI0) as "#>Hwp".
  iDestruct "Hwp" as (e_s Hsim) "#Hwp /=".
  iSpecialize ("Hwp" $! ids with "[//]").
  rewrite hsubst_id (wptp_safe_n n).
  iIntros "!>!>"; iDestruct ("Hwp") as %Hsafe; naive_solver.
Qed.

Corollary unstamped_safety_dot_sem Σ `{HdlangG: !dlangPreG Σ} `{!SwapPropI Σ}
  {e T}
  (Hlog : ∀ `(!dlangG Σ) `(!SwapPropI Σ), ⊢ [] u⊨ e : T):
  safe e.
Proof. exact: (unstamped_s_safety_dot_sem Σ (λ _, V⟦T⟧)). Qed.
