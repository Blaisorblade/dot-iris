(** * Semantic typing for positive numbers and division.
The main result is [posModTy]. *)
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting adequacy.
From iris.program_logic Require Import ectxi_language.

From D Require Import swap_later_impl.
From D.Dot Require Import syn_lemmas.
From D.Dot Require Import ex_iris_utils sem_unstamped_typing.

Import dlang_adequacy.

Set Suggest Proof Using.
Set Default Proof Using "Type".

Implicit Types (v w : vl) (d : dm) (ds : dms).

(** ** Example code. *)
Section examplesBodies.
  Import hoasNotation.

  Definition hdivV := λ: m n, m `div` (htskip n).
  Definition hmkPosBodyV (n : hvl) := htif (n > 0) n hloopTm.
  Definition hmkPosV := λ: n, hmkPosBodyV n.

  Definition hposModV : hvl := ν: _ , {@
    type "Pos" = 𝐙;
    val "mkPos" = hmkPosV;
    val "div" = hdivV
  }.

  Definition hposModTTail self : hty := {@
    val "mkPos" : 𝐙 →: self @; "Pos";
    val "div" : 𝐙 →: self @; "Pos" →: 𝐙
  }.

  Definition hposModTBody self : hty := {@
    type "Pos" >: ⊥ <: 𝐙;
    val "mkPos" : 𝐙 →: self @; "Pos";
    val "div" : 𝐙 →: self @; "Pos" →: 𝐙
  }.

  Example testEq x :
    hposModTBody x = hTAnd (type "Pos" >: ⊥ <: 𝐙) (hposModTTail x) :=
    reflexivity _.

  (** Actual type *)
  Definition hposModT := μ: self, hposModTBody self.
End examplesBodies.

Local Hint Constructors bin_op_syntype cond_bin_op_syntype : core.
Local Hint Extern 1000 => lia : core.

Ltac wp_bin_base := iApply wp_bin; first eapply cond_bin_op_syntype_sound; by [cbn; eauto|].
Ltac wp_bin := iApply wp_wand; [wp_bin_base | iIntros].

Local Open Scope Z_scope.

  Import hoasNotation.

(* Generic useful lemmas — not needed for fundamental theorem,
    but very useful for examples. *)
Section helpers.
  Context `{HdlangG: !dlangG Σ}.

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
End helpers.

Definition pos v := ∃ n, v = vint n ∧ n > 0.
Definition ipos {Σ}: oltyO Σ 0 := olty0 (λI ρ v, ⌜ pos v ⌝).

Definition s_is_pos `{!dlangG Σ} s : iProp Σ := s ↝n[ 0 ] ipos.

Section div_example.
  Context `{HdlangG: !dlangG Σ} `{SwapPropI Σ}.

  Lemma wp_if_ge (n : Z) :
    ⊢ WP hmkPosBodyV n {{ w, ⌜ w = n ∧ n > 0 ⌝}}.
  Proof using Type*.
    wp_bind (IfCtx _ _).
    wp_bin; ev; simplify_eq/=.
    case_decide; wp_pure; first by auto.
    iApply wp_wand; [iApply loopSemT | naive_solver].
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

  Lemma sStp_ipos_nat Γ i : ⊢ Γ s⊨ ipos <:[ i ] V⟦ 𝐙 ⟧.
  Proof. iIntros "!> * _ !%"; rewrite /pos /pure_interp_prim; naive_solver. Qed.

  Lemma posTMem_widen Γ l i : ⊢ Γ s⊨ cTMemL l ipos ipos <:[ i ] cTMemL l ⊥ oInt.
  Proof using Type*.
    iApply sTyp_Stp_Typ; iApply sLater_Stp_Eq; [iApply sBot_Stp | iApply sStp_ipos_nat].
  Qed.

  Lemma suD_posDm_ipos l Γ : ⊢ Γ su⊨ { l := dtysyn TInt } : cTMemL l ipos ipos.
  Proof.
    by iApply (suD_Typ_Abs (σ := []) (T := ipos) TInt); [|iApply sStp_Refl..].
  Qed.

  Lemma sD_posDm_abs l Γ : ⊢ Γ su⊨ { l := dtysyn TInt } : cTMemL l ⊥ oInt.
  Proof using Type*.
    iApply (suD_Typ_Stp (oLater ipos)); last iApply suD_posDm_ipos; iApply sLater_Stp_Eq;
      [iApply sBot_Stp | iApply sStp_ipos_nat].
  Qed.

  Local Definition cPreciseBody :=
    cAnd (cTMemL "Pos" ipos ipos) C⟦ hposModTTail hx0 ⟧.
  Local Definition oPreciseBody : olty Σ 0 := clty_olty cPreciseBody.

  (**
  Show that our program is semantically well-typed,
  using the semantic unstamped typing judgment.
  *)
  Theorem posModTy : ⊢ [] u⊨ hposModV : hposModT.
  Proof using Type*.
    rewrite /hposModT.
    have HctxSub:
      s⊨G oLater cPreciseBody :: V⟦ [] ⟧* <:* oLater <$> [oPreciseBody].
    by iIntros "% $".
    iApply (suT_DSub (T1 := oMu oPreciseBody)); first last. {
      iApply sMu_Stp_Mu. rewrite oLaterN_0.
      iApply sStp_And; [| iApply sAnd2_Stp ].
      iApply sStp_Trans; first iApply sAnd1_Stp.
      iApply posTMem_widen.
    }
    iApply suT_Obj_I.
    iApply suD_Cons; [done|iApply suD_posDm_ipos|].
    iApply suD_Cons; [done| iApply suD_Val|]; last
      (iApply suD_Cons; [done| iApply suD_Val |iApply suD_Nil]);
      iApply (suT_All_I_Strong _ _ _ HctxSub).
    - iIntros "!>"; unstamp_goal_tm.
      iIntros "!> %ρ [[_ [#Hpos _]] %Hnpos] !>"; lazy in Hnpos.
      case: Hnpos => [n Hw].
      iApply wp_wand; [rewrite /= {}Hw; iApply wp_if_ge |
        iIntros (v [-> Hnpos])].
      iEval rewrite /= path_wp_pv_eq.
      iApply (vl_sel_lb with "[] Hpos").
      iIntros "!%"; hnf. naive_solver.
    - iApply suT_All_I.
      iIntros "!>"; unstamp_goal_tm.
      iIntros "!> %ρ #[[[_ [Hpos _]] Hw] Harg] !>".
      rewrite /shead /stail. iSimpl.
      iDestruct "Hw" as %[m ->].
      setoid_rewrite path_wp_pv_eq.
      iPoseProof (vl_sel_ub with "Harg Hpos") as "{Harg} Harg".
      wp_bind (BinRCtx _ _); iEval rewrite /=/lang.of_val.
      rewrite -wp_pure_step_later // -wp_value'; iNext.
      iApply (wp_div_spec with "Harg").
  Qed.
End div_example.

(**
An example of how to apply adequacy to get safety.
This theorem is actually not interesting, because safety of a value is trivial,
but thanks to semantic typing lemmas, we can instead show semantic typing of
closed clients of [hposModV] that aren't values, and then apply adequacy to
obtain their safety.
*)
Lemma posModVSafe : safe hposModV.
Proof.
  apply (unstamped_safety_dot_sem dlangΣ (T := hposModT))=>*.
  apply posModTy.
Qed.
