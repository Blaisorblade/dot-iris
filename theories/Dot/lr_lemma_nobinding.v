From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

Section Sec.
  Context `{HdotG: dotG Σ} Γ.

  Lemma Sub_Mono T i :
    (Γ ⊨ [T, i] <: [T, S i])%I.
  Proof. by iIntros "!> **". Qed.

  Lemma swap_later {n} {PROP: sbi} (P : PROP): ▷^n ▷ P ⊣⊢ ▷ ▷^n P.
  Proof. iSplit; by iIntros "H !>!>". Qed.

  Lemma Sub_Later_Sub T1 T2 i:
    Γ ⊨ [T1, S i] <: [T2, S i] -∗
    Γ ⊨ [TLater T1, i] <: [TLater T2, i].
  Proof.
    iIntros "/= #Hsub !>" (ρ v Hclv) "#Hg #[_ HT1]"; iFrame "%".
    iSpecialize ("Hsub" $! _ v Hclv with "Hg").
    rewrite !swap_later.
    by iApply "Hsub".
  Qed.

  Lemma Sub_TVMem_Covariant T1 T2 i l:
    ▷^(S i) (Γ ⊨ [T1, 0] <: [T2, 0]) -∗
    ▷^i (Γ ⊨ [TVMem l T1, 0] <: [TVMem l T2, 0]).
  Proof.
    iIntros "#HsubT /= !>!>" (ρ v Hcl) "#Hg [$ #HT1]".
    iDestruct "HT1" as (d) "#[Hdl [Hcld #HT1]]".
    iExists d; repeat iSplit => //.
    iDestruct "HT1" as (vmem) "[Heq HvT1]".
    iExists vmem; repeat iSplit => //.
    iApply "HsubT" => //.
    by iApply interp_v_closed.
  Qed.

  Lemma Sub_TMem_Variant L1 L2 U1 U2 i l:
    ▷^(S i)(Γ ⊨ [L2, 0] <: [L1, 0]) -∗
    ▷^(S i)(Γ ⊨ [U1, 0] <: [U2, 0]) -∗
    ▷^i (Γ ⊨ [TTMem l L1 U1, 0] <: [TTMem l L2 U2, 0]).
  Proof.
    iIntros "#HsubT #HsubU /= !>!>" (ρ v Hcl) "#Hg [$ #HT1]".
    iDestruct "HT1" as (d) "#[Hdl [Hcld #HT1]]".
    iExists d; repeat iSplit => //.
    iDestruct "HT1" as (φ) "[Heq #[HLφ HφU]]".
    iExists φ; repeat iSplit => //.
    iModIntro; iSplitL; iIntros (w Hclw) "#H".
    - iApply "HLφ" => //. by iApply "HsubT".
    - iApply "HsubU" => //. by iApply "HφU".
  Qed.

  Lemma Later_Sub T i :
    (Γ ⊨ [TLater T, i] <: [T, S i])%I.
  Proof. by iIntros "/= !>" (ρ v Hclv) "#HG #[Hcl HT] !>". Qed.

  Lemma Sub_Later T i :
    (Γ ⊨ [T, S i] <: [TLater T, i])%I.
  Proof. iIntros "/= !> ** !>". naive_solver. Qed.

  Lemma Sub_Index_Incr T U i j:
    (Γ ⊨ [T, i] <: [U, j] →
     Γ ⊨ [T, S i] <: [U, S j])%I.
  Proof. iIntros "/= #Hsub !> ** !>". by iApply "Hsub". Qed.

  Lemma And1_Sub T1 T2 i: Γ ⊨ [TAnd T1 T2, i] <: [T1, i].
  Proof. by iIntros "/= !> * ? ? [? ?]". Qed.
  Lemma And2_Sub T1 T2 i: Γ ⊨ [TAnd T1 T2, i] <: [T2, i].
  Proof. by iIntros "/= !> * ? ? [? ?]". Qed.

  (* Lemma stp_andi T1 T2 ρ v: *)
  (*   ⟦T1⟧ ρ v -∗ *)
  (*   ⟦T2⟧ ρ v -∗ *)
  (*   ⟦TAnd T1 T2⟧ ρ v. *)
  (* Proof. iIntros; by iSplit. Qed. *)

  Lemma Sub_And S T1 T2 i j:
    Γ ⊨ [S, i] <: [T1, j] -∗
    Γ ⊨ [S, i] <: [T2, j] -∗
    Γ ⊨ [S, i] <: [TAnd T1 T2, j].
  Proof.
    iIntros "/= #H1 #H2 !> * #Hcl #Hg #HS".
    iSpecialize ("H1" with "Hcl Hg HS").
    iSpecialize ("H2" with "Hcl Hg HS").
    iModIntro; by iSplit.
  Qed.

  Lemma Sub_Or1 T1 T2 i: Γ ⊨ [T1, i] <: [TOr T1 T2, i].
  Proof. iIntros "/= !> ** !>"; naive_solver. Qed.
  Lemma Sub_Or2 T1 T2 i: Γ ⊨ [T2, i] <: [TOr T1 T2, i].
  Proof. iIntros "/= !> ** !>"; naive_solver. Qed.

  Lemma Or_Sub S T1 T2 i j:
    Γ ⊨ [T1, i] <: [S, j] -∗
    Γ ⊨ [T2, i] <: [S, j] -∗
    Γ ⊨ [TOr T1 T2, i] <: [S, j].
  Proof. iIntros "/= #H1 #H2 !> * #Hcl #Hg #[HT1 | HT2]"; by [iApply "H1" | iApply "H2"]. Qed.

  Lemma Sub_Top T i:
    Γ ⊨ [T, i] <: [TTop, i].
  Proof. by iIntros "!> ** /=". Qed.

  Lemma Bot_Sub T i:
    Γ ⊨ [TBot, i] <: [T, i].
  Proof. by iIntros "/= !> ** !>". Qed.

  Lemma T_Nat_I n: Γ ⊨ tv (vnat n): TNat.
  Proof.
    iSplit => //; iIntros "!> ** /="; iApply wp_value; naive_solver.
  Qed.
End Sec.
