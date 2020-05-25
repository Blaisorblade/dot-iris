(** * Semantic typing for positive numbers and division. *)
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting adequacy.
From iris.program_logic Require Import ectxi_language.

From D Require Import swap_later_impl.
From D.Dot Require Import syn_lemmas.
From D.Dot Require Import ex_iris_utils.
From D.Dot Require Import scala_lib hoas ex_utils storeless_typing_ex_utils.

Import dlang_adequacy.

Set Suggest Proof Using.
Set Default Proof Using "Type".

Implicit Types (v w : vl) (d : dm) (ds : dms).

Import hoas.syn.

(** ** Example code. *)
Section examplesBodies.
  Import hoasNotation.

  Definition hdivV := λ: m n, m `div` (htskip n).
  Definition hmkPosBodyV (n : hvl) := htif (n > 0) n hloopTm.
  Definition hmkPosV := λ: n, hmkPosBodyV n.

  Definition hposModV s : hvl := ν: _ , {@
    type "Pos" = ([]; s);
    val "mkPos" = hmkPosV;
    val "div" = hdivV
  }.

  (** Actual type *)
  Definition posModT := μ: self, {@
    type "Pos" >: ⊥ <: 𝐙;
    val "mkPos" : 𝐙 →: self @; "Pos";
    val "div" : 𝐙 →: self @; "Pos" →: 𝐙
  }.
End examplesBodies.

Local Hint Constructors bin_op_syntype cond_bin_op_syntype : core.
Local Hint Extern 1000 => lia : core.

Ltac wp_bin_base := iApply wp_bin; first eapply cond_bin_op_syntype_sound; by [cbn; eauto|].
Ltac wp_bin := iApply wp_wand; [wp_bin_base | iIntros].
Import stamp_transfer.

Local Open Scope Z_scope.

(* Generic useful lemmas — not needed for fundamental theorem,
    but very useful for examples. *)
Section helpers.
  Context `{HdlangG: !dlangG Σ}.

  Lemma alloc {s sγ} φ : sγ !! s = None → allGs sγ ==∗ s ↝n[ 0 ] φ.
  Proof.
    iIntros (Hs) "Hsγ".
    by iMod (leadsto_alloc φ Hs with "Hsγ") as (?) "[_ [_ $]]".
  Qed.
  Lemma wp_ge m n (Hge : m > n) : ⊢ WP m > n {{ w, w ≡ true }}.
  Proof. wp_bin. ev; simplify_eq/=. case_decide; by [|lia]. Qed.
  Lemma wp_nge m n (Hnge : ¬ m > n) : ⊢ WP m > n {{ w, w ≡ false }}.
  Proof. wp_bin. ev; simplify_eq/=. case_decide; by [|lia]. Qed.

  Lemma setp_value Γ (T : olty Σ 0) v: Γ s⊨ v : T ⊣⊢ (□∀ ρ, sG⟦ Γ ⟧* ρ → T vnil ρ v.[ρ]).
  Proof.
    rewrite /=; properness => //; iSplit;
      [rewrite wp_value_inv|rewrite -wp_value]; iIntros "#$".
  Qed.

  Lemma setp_value_eq (T : olty Σ 0) v: (∀ ρ, T vnil ρ v.[ρ]) ⊣⊢ [] s⊨ v : T.
  Proof.
    iSplit.
    - iIntros "#H !>" (? _).
      rewrite /= -wp_value'. iApply "H".
    - iIntros "/= H" (ρ).
      iSpecialize ("H" $! ρ with "[//]").
      by rewrite /= wp_value_inv'.
  Qed.

  Lemma ietp_value_eq T v: (∀ ρ, ⟦ T ⟧ ρ v.[ρ]) ⊣⊢ [] ⊨ v : T.
  Proof. apply setp_value_eq. Qed.

  Lemma ietp_value T v: (∀ ρ, ⟦ T ⟧ ρ v.[ρ]) -∗ [] ⊨ v : T.
  Proof. by rewrite ietp_value_eq. Qed.

  Lemma ietp_value_inv T v : [] ⊨ v : T -∗ ∀ ρ, ⟦ T ⟧ ρ v.[ρ].
  Proof. by rewrite ietp_value_eq. Qed.

  Lemma V_TVMem_I T v w l
    (Hclv : nclosed_vl v 0)
    (Hlook : v @ l ↘ (dpt (pv w))) :
    [] ⊨ w : T -∗
    [] ⊨ v : TVMem l T.
  Proof.
    have Hclw: nclosed_vl w 0.
    by have := nclosed_lookup' Hlook Hclv; eauto with fv.
    iIntros "#H"; iApply ietp_value; iIntros (ρ).
    iSpecialize ("H" $! ρ with "[//]").
    rewrite /interp_expr wp_value_inv !closed_subst_vl_id //.
    iExists _; iFrame (Hlook); by rewrite oDVMem_eq path_wp_pv_eq.
  Qed.
End helpers.

Ltac valMember ρ :=
  iApply V_TVMem_I; [solve_fv_congruence|naive_solver|
    rewrite -ietp_value; iIntros (ρ)].

Definition pos v := ∃ n, v = vint n ∧ n > 0.
Definition ipos {Σ}: oltyO Σ 0 := olty0 (λI ρ v, ⌜ pos v ⌝).

Definition s_is_pos `{!dlangG Σ} s : iProp Σ := s ↝n[ 0 ] ipos.

Section div_example.
  Context `{HdlangG: !dlangG Σ} `{SwapPropI Σ}.
  Context (s: stamp).

  Definition posModV : vl := hposModV s.

  Notation Hs := (s_is_pos s).
  Lemma allocHs sγ:
    sγ !! s = None → allGs sγ ==∗ Hs.
  Proof. exact (alloc ipos). Qed.

  Lemma wp_if_ge (n : Z) :
    ⊢ WP hmkPosBodyV n {{ w, ⌜ w = n ∧ n > 0 ⌝}}.
  Proof using Type*.
    wp_bind (IfCtx _ _).
    wp_bin; ev; simplify_eq/=.
    case_decide; wp_pure; first by auto.
    iApply wp_wand; [iApply loopSemT | naive_solver].
  Qed.

  (** We assume [Hs] throughout the rest of the section. *)

  Definition posDm := dtysem [] s.
  Definition testVl l : vl := ν {@ (l, posDm) }.

  Lemma sToIpos : Hs -∗ posDm ↗n[ 0 ] hoEnvD_inst [] ipos.
  Proof. by iApply dm_to_type_intro. Qed.


  Lemma Sub_ipos_nat Γ : ⊢ Γ s⊨ ipos, 0 <: V⟦ 𝐙 ⟧, 0.
  Proof. iIntros "!> * _ !%"; rewrite /pos /pure_interp_prim; naive_solver. Qed.

  Lemma Sub_later_ipos_nat Γ : ⊢ Γ s⊨ oLater ipos, 0 <: oLater V⟦ 𝐙 ⟧, 0.
  Proof. rewrite -sSub_Later_Sub -sSub_Index_Incr. apply Sub_ipos_nat. Qed.

  Lemma posTMem_widen Γ l : ⊢ Γ s⊨ cTMemL l ipos ipos, 0 <: cTMemL l ⊥ oInt, 0.
  Proof using Type*.
    iApply sTyp_Sub_Typ; [iApply sBot_Sub | iApply Sub_later_ipos_nat].
  Qed.


  Lemma sD_posDm_ipos l Γ : Hs -∗ Γ s⊨ { l := posDm } : cTMemL l ipos ipos.
  Proof.
    iIntros "Hs".
    iApply (sD_Typ_Abs ipos); [iApply sSub_Refl..|by iExists _; iFrame "Hs"].
  Qed.

  Lemma sD_posDm_abs l Γ : Hs -∗ Γ s⊨ { l := posDm } : cTMemL l ⊥ oInt.
  Proof.
    iIntros "Hs"; iApply (sD_Typ_Sub (oLater ipos));
      [iApply sBot_Sub|iApply Sub_later_ipos_nat|iApply (sD_posDm_ipos with "Hs")].
  Qed.

  Lemma sInTestVl l ρ : path_includes (pv x0) (testVl l .: ρ) [(l, posDm)].
  Proof. constructor; naive_solver. Qed.

  Lemma s_posDm l : Hs -∗ cTMemL l ipos ipos ids [(l, posDm)].
  Proof.
    rewrite (sD_posDm_ipos l []) sdtp_eq; iIntros "H".
    iApply ("H" $! (testVl l .: ids) with "[] [//]"); auto using sInTestVl.
  Qed.

  Lemma posModVHasA ρ :
    Hs -∗ clty_olty (cTMemL "Pos" ipos ipos) vnil ρ posModV.[ρ].
  Proof. by rewrite (s_posDm "Pos") -clty_commute. Qed.

  Lemma posModVHasATy: Hs -∗ [] s⊨ posModV : cTMemL "Pos" ipos ipos.
  Proof.
    rewrite -setp_value_eq; iIntros "#Hs %ρ"; iApply (posModVHasA ρ with "Hs").
  Qed.

  Lemma posModVHasATyAbs: Hs -∗ [] ⊨ posModV : type "Pos" >: ⊥ <: TInt.
  Proof using Type*.
    iIntros "Hs"; iApply (sT_Sub (i := 0) with "[Hs]");
      [iApply (posModVHasATy with "Hs") | iApply posTMem_widen].
  Qed.

  Lemma ty_mkPos :
    ⊢ [] s⊨ hmkPosV : oAll V⟦ 𝐙 ⟧ (olty0 (λI ρ v, ⌜ ∃ n : Z, v = n ∧ n > 0 ⌝)).
  Proof using Type*.
    rewrite -sT_All_I /= /shead.
    iIntros (ρ) "!> /=". iDestruct 1 as %(_ & n & Hw); simplify_eq/=; rewrite Hw.
    iIntros "!>". iApply wp_wand; [iApply wp_if_ge | naive_solver].
  Qed.

  Lemma wp_mkPos :
    ⊢ oAll V⟦ 𝐙 ⟧ (olty0 (λI ρ v, ⌜ ∃ n : Z, v = n ∧ n > 0 ⌝)) vnil ids hmkPosV.
  Proof using Type*. iApply wp_value_inv'. iApply (ty_mkPos with "[//]"). Qed.

  Lemma wp_div_spec (m : Z) w : ipos vnil ids w -∗ WP m `div` w {{ ⟦ 𝐙 ⟧ ids }}.
  Proof. iDestruct 1 as %(n&?&?); simplify_eq. wp_bin. by iIntros "!%"; naive_solver. Qed.

  Close Scope Z_scope.

  Lemma posModTy: Hs -∗ [] ⊨ posModV : posModT.
  Proof using Type*.
    rewrite /posModT -(T_Mu_I _ posModV).
    iIntros "#Hs".
    iApply sT_And_I; first by iApply posModVHasATyAbs.
    iApply sT_And_I; last iApply sT_And_I; last by
      iIntros "!> ** /="; rewrite -wp_value'.
    - iApply V_TVMem_I; [solve_fv_congruence|naive_solver|].
      iApply sT_All_I.
      rewrite /= /shead.
      iIntros "!>" (ρ [_ [n Hw]]) "!> /="; simpl in *; rewrite {}Hw.
      iApply wp_wand; [iApply wp_if_ge |iIntros "/=" (v [-> Hnpos])].
      rewrite path_wp_pv_eq.
      iApply vl_sel_lb; last iApply (posModVHasA ids with "Hs").
      iIntros "!%"; hnf. naive_solver.
    - iApply V_TVMem_I; [solve_fv_congruence|naive_solver|].
      iApply sT_All_I.
      iApply sT_All_I.
      rewrite /= /shead /stail/=.
      iIntros "!> %ρ #[[_ Hw] Harg] !> /=".
      iDestruct "Hw" as %[m ->].
      setoid_rewrite path_wp_pv_eq.
      iPoseProof (vl_sel_ub with "Harg []") as "{Harg Hs} Harg".
      by iApply (posModVHasA ids with "Hs").
      wp_bind (BinRCtx _ _); iEval rewrite /=/lang.of_val.
      rewrite -wp_pure_step_later // -wp_value'; iNext.
      iApply (wp_div_spec with "Harg").
  Qed.
End div_example.

Lemma posModVSafe (s : stamp): safe (posModV s).
Proof.
  eapply (safety_dot_sem dlangΣ (T := posModT))=>*.
  by rewrite (allocHs s) // -posModTy.
Qed.
