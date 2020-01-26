From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting adequacy.
From D.Dot Require Import unary_lr
  lr_lemmas lr_lemmasNoBinding lr_lemmasDefs lr_lemmasPrim.
From D.Dot Require Import skeleton fundamental.
From D.Dot Require Import scalaLib hoas exampleInfra typingExInfra.

Import hoasNotation.

Example loopDefTyp Γ : Γ v⊢ₜ[ ∅ ] hclose (htv hloopDefV) : hclose hloopDefT.
Proof.
  apply (Subs_typed_nocoerce (hclose hloopDefTConcr)); mltcrush. cbv.

  eapply App_typed; last var.
  tcrush; varsub; lookup.
Qed.

Example loopFunTyp Γ : Γ v⊢ₜ[∅] hclose hloopFunTm : hclose ⊤ →: ⊥.
Proof. have ? := loopDefTyp Γ; tcrush. Qed.

Example loopTyp Γ : Γ v⊢ₜ[∅] hclose hloopTm : ⊥.
Proof.
  have ? := loopFunTyp Γ; apply (App_typed (T1 := ⊤)), (Subs_typed_nocoerce 𝐍); tcrush.
Qed.

(** XXX Not currently using olty. *)
Module example.
Section ex.
  Context `{HdlangG: dlangG Σ}.

  Import stamp_transfer.

  Lemma alloc {s sγ} (φ : envD Σ) : sγ !! s = None → allGs sγ ==∗ s ↝ φ.
  Proof.
    iIntros (Hs) "Hsγ".
    by iMod (leadsto_alloc φ Hs with "Hsγ") as (?) "[_ [_ $]]".
  Qed.

  Definition pos v := ∃ n, v = vnat n ∧ n > 0.
  Definition ipos: envD Σ := λ ρ v, (⌜ pos v ⌝) %I.
  Import ectxi_language ectx_language.

(* Arguments dlang_ectx_lang : simpl never.
Arguments dlang_ectxi_lang : simpl never. *)

  Ltac wp_bin_base := iApply wp_bin; first eapply bin_op_syntype_sound; by [|constructor].
  Ltac wp_bin := iApply wp_wand; [wp_bin_base | iIntros].
  Tactic Notation "wp_bind" uconstr(p) := iApply (wp_bind (fill [p])).

  Lemma wp_ge m n (Hge : m > n) : WP m > n {{ w, w ≡ true }}%I.
  Proof. wp_bin. ev; simplify_eq/=. by case_decide. Qed.
  Lemma wp_nge m n (Hnge : ¬ m > n) : WP m > n {{ w, w ≡ false }}%I.
  Proof. wp_bin. ev; simplify_eq/=. by case_decide. Qed.

  Lemma pos_wp ρ v : ipos ρ v ⊢ WP v > 0 {{ w, w ≡ vbool true }}.
  Proof. iDestruct 1 as %(n & -> & ?). by iApply wp_ge. Qed.

  Import swap_later_impl.
  Context `{SwapPropI Σ}.
  Lemma loopSemT: (WP hclose hloopTm {{ _, False }})%I.
  Proof.
    iDestruct (fundamental_typed _ _ _ _ (loopTyp []) with "[]") as "H".
    iApply wellMappedφ_empty.
    iSpecialize ("H" $! ids with "[//]").
    by rewrite hsubst_id /=.
  Qed.

  Definition hmkPosBodyV n := htif (n > 0) n hloopTm.
  Definition hmkPosV := λ: n, hmkPosBodyV n.
  Lemma wp_if_ge (n : nat) :
    WP hclose (hmkPosBodyV n) {{ w, ⌜ w = n ∧ n > 0 ⌝}}%I.
  Proof.
    wp_bind (IfCtx _ _).
    wp_bin; ev; simplify_eq/=.
    case_decide; rewrite -wp_pure_step_later //; iNext.
    by rewrite -wp_value'.
    iApply wp_wand; [iApply loopSemT | naive_solver].
  Qed.

  Lemma wp_if_ge' (n : nat) :
    WP tif (n > 0) (1 `div` n) (hclose hloopTm) {{ w, ⟦ 𝐍 ⟧ ids w ∧ ⌜ n > 0 ⌝}}%I.
  Proof.
    wp_bind (IfCtx _ _).
    wp_bin; ev; simplify_eq/=.
    case_decide; rewrite -wp_pure_step_later //; iNext.
    - wp_bin. naive_solver.
    - iApply wp_wand; [iApply loopSemT | naive_solver].
  Qed.

  Context (s: stamp).

  Definition Hs := (s ↝ ipos)%I.
  Lemma allocHs sγ:
    sγ !! s = None → allGs sγ ==∗ Hs.
  Proof. exact (alloc ipos). Qed.

  (* Experiments using fancier infrastructure: *)
  Lemma allocHsGen sγ:
    sγ !! s = None → allGs sγ ==∗ Hs.
  Proof.
    iIntros (Hl) "H". iApply wellMappedφ_apply;
      last iApply (transfer (<[s:=ipos]> ∅) with "H") => s';
      rewrite ?lookup_insert ?dom_insert ?dom_empty //; set_solver.
  Qed.

  Lemma allocHs1: allGs ∅ ==∗ Hs.
  Proof.
    iIntros "H"; iApply wellMappedφ_apply; last iApply (transfer_empty (<[s:=ipos]> ∅) with "H").
    by rewrite lookup_insert.
  Qed.

  (* Generic useful lemmas — not needed for fundamental theorem,
     but very useful for examples. *)
  Lemma ietp_value T v: (∀ ρ, ⟦ T ⟧ ρ v.[ρ]) -∗ [] ⊨ tv v : T.
  Proof.
    iIntros "#H /= !>" (? _).
    rewrite -wp_value'. iApply "H".
  Qed.

  Lemma ietp_value_inv T v: [] ⊨ tv v : T -∗ ∀ ρ, ⟦ T ⟧ ρ v.[ρ].
  Proof.
    iIntros "/= H" (ρ).
    iSpecialize ("H" $! ρ with "[//]").
    by rewrite wp_value_inv'.
  Qed.


  Import hoasNotation.

  Definition posModT := μ: self, {@
    type "Pos" >: ⊥ <: 𝐍;
    val "mkPos" : 𝐍 →: self @; "Pos";
    val "div" : 𝐍 →: self @; "Pos" →: 𝐍
  }.

  Definition hdivV := λ: m n, (htskip m) `div` n.

  (** Under Iris assumption [Hs], [v.A] points to [ipos].
      We assume [Hs] throughout the rest of the section. *)
  Import DBNotation.

  Definition posModV := ν {@
    type "Pos" = ([]; s);
    val "mkPos" = pv (hclose hmkPosV);
    val "div" = pv (hclose hdivV)
  }.

  Definition v := ν {@
    type "A" = ([]; s);
	  val "n" = pv (vnat 2)
  }.

  Lemma sToIpos : Hs -∗ dtysem [] s ↗ ipos (∞ []).
  Proof. by iApply dm_to_type_intro. Qed.

  Lemma sHasA : Hs -∗ def_interp_tmem ⟦ ⊥ ⟧ ⟦ 𝐍 ⟧ ids (dtysem [] s).
  Proof.
    iIntros; cbn; repeat (repeat iExists _; repeat iSplit; try done).
    by iApply sToIpos.
    iModIntro; repeat iSplit; iIntros (w). by iIntros ">[]".
    iMod 1 as %(n & -> & ?). iPureIntro.
    rewrite /pure_interp_prim /prim_evals_to /=. eauto.
  Qed.

  Lemma wp_mkPos :
    interp_forall ⟦ 𝐍 ⟧ (λ ρ v, ⌜ ∃ n : nat, v = n ∧ n > 0 ⌝)%I ids (hclose hmkPosV).
  Proof.
    repeat (iExists _; iSplit => //).
    iIntros (w) "!>"; iMod 1 as %[n Hw]; iIntros "!> !>".
    simplify_eq/=.
    iApply wp_wand; [iApply wp_if_ge | iIntros "!% /="].
    naive_solver.
  Qed.

  (** Yes, v has a valid type member. *)
  Lemma vHasA0: Hs -∗ ∀ ρ, ⟦ type "A" >: ⊥ <: TNat ⟧ ρ v.[ρ].
  Proof.
    iIntros "#Hs" (ρ); iExists _; iSplit; by [eauto | iApply sHasA].
  Qed.

  Lemma posModVHasA0: Hs -∗ ∀ ρ, ⟦ type "Pos" >: ⊥ <: TNat ⟧ ρ posModV.[ρ].
  Proof. iIntros "#Hs" (ρ); iExists _; iSplit; by [eauto | iApply sHasA]. Qed.

  Lemma vHasA0typ: Hs -∗ [] ⊨ tv v : type "A" >: ⊥ <: 𝐍.
  Proof. rewrite -ietp_value. iApply vHasA0. Qed.

  Definition vTyp1 := μ {@
    type "A" >: ⊥ <: 𝐍;
    val "n" : p0 @; "A"
  }.

  Lemma wp_div_spec (m : nat) w : ipos ids w -∗ WP m `div` w {{ ⟦ 𝐍 ⟧ ids }}.
  Proof. iDestruct 1 as %(n&?&?); simplify_eq. wp_bin. by iIntros "!%"; naive_solver. Qed.

  Lemma V_TVMem_I T (v w : vl) l
    (Hclv : nclosed_vl v 0)
    (* XXX should be (Hlook : w @ l ↘ (dpt (pv v))) *)
    (Hlook : objLookup v l (dpt (pv w))):
    [] ⊨ tv w : T -∗
    [] ⊨ v : TVMem l T.
  Proof.
    Import synLemmas.
    have Hclw: nclosed_vl w 0.
    by have := nclosed_lookup' Hlook Hclv; eauto with fv.
    iIntros "#H"; iApply ietp_value; iIntros (ρ) "/=".
    iSpecialize ("H" $! ρ with "[//]"). rewrite wp_value_inv.
    rewrite !closed_subst_vl_id //.
    do 2 (iExists _; iSplit; [done|]).
    by rewrite path_wp_pv.
  Qed.

  Ltac valMember ρ :=
    iApply V_TVMem_I; [solve_fv_congruence|naive_solver|
      rewrite -ietp_value; iIntros (ρ)].

  Lemma posModVHasA: Hs -∗ [] ⊨ posModV : hclose posModT.
  Proof.
    rewrite /posModT -(TMu_I [] _ posModV).
    iIntros "#Hs". cbn -[ietp].
    iApply TAnd_I; first by rewrite -ietp_value -posModVHasA0.
    iApply TAnd_I; last iApply TAnd_I; last by
      iIntros "!> ** /="; rewrite -wp_value'.
    - valMember ρ; iExists _; iSplit; [done|].
      iIntros (w) "!>"; iMod 1 as %[n Hw]; iIntros "!> !>".
      simplify_eq/=.
      iApply wp_wand; [iApply wp_if_ge | iIntros "/=" (v [-> ?])].
      rewrite path_wp_pv.
      repeat (iExists _; try iSplit => //=).
      iSplit => //. by iApply dm_to_type_intro.
      iIntros "!%"; rewrite /pos.
      naive_solver.
    - valMember ρ; iExists _; iSplit; [done|].
      iIntros (v) "!>"; iMod 1 as %[m Hw]; iIntros "!> !>".
      rewrite -wp_value'; simplify_eq/=; iExists _; iSplit; [done|].
      iIntros (w) "!> #Harg!>!>"; rewrite path_wp_pv /=.
      iDestruct "Harg" as (Φ d [ds Hlook]) "[Hs1 #Harg]";
        have {d ds Hlook}->: d = dtysem [] s by naive_solver.
      iPoseProof (sToIpos with "Hs") as "Hs2/=".
      iPoseProof (dm_to_type_agree _ _ _ w with "Hs1 Hs2") as "{Hs Hs1 Hs2} Heq".
      wp_bind (BinLCtx _ _); rewrite -wp_pure_step_later // -wp_value/=/lang.of_val.
      iNext. iRewrite "Heq" in "Harg"; iClear "Heq".
      by iApply wp_div_spec.
  Qed.

  (* This works. Crucially, we use TMu_I to introduce the object type.
     This way, we can inline the object in the type selection.
     This cannot be done using T_New_I directly.
     However, this is closer to how typechecking in Scala
     actually works.
     XXX: also, maybe this *could* be done with T_New_I with
     a precise type? That'd be a more correct derivation.
   *)
  Lemma vHasA1: Hs -∗ ∀ ρ, ⟦ vTyp1 ⟧ ρ v.[ρ].
  Proof.
    rewrite -ietp_value_inv -(TMu_I [] _ v).
    iIntros "#Hs".
    iApply TAnd_I; first by [iApply vHasA0typ].
    iApply TAnd_I; first last.
    - iApply (T_Sub _ _ _ _ 0); last by iApply Sub_Top.
      by iApply vHasA0typ.
    - rewrite -ietp_value /=.
      have Hev2: pos (vnat 2) by rewrite /pos; eauto.
      iIntros (_).

      repeat (repeat iExists _; repeat iSplit; rewrite ?path_wp_pv //);
        try by [|iApply dm_to_type_intro].
  Qed.

  Lemma vHasA1t : Hs -∗ [] ⊨ tv v : vTyp1.
  Proof. rewrite -ietp_value. iApply vHasA1. Qed.

  Lemma vHasA1TypAd : allGs ∅ ==∗ [] ⊨ tv v : vTyp1.
  Proof. rewrite -ietp_value allocHs //; iIntros. by iApply vHasA1. Qed.

  (* Lemma vHasA1': Hs -∗ ∀ ρ, ⟦ vTyp1 ⟧ ρ v.[ρ].
  Proof.
    rewrite -ietp_value_inv. iIntros "#Hs".
    (* Fails, because we need a *syntactic* type. *)
    iApply (T_Sub [] v _ vTyp1 0). *)

  (*
    A different approach would be to type the object using T_New_I
    with an object type [U] with member [TTMem "A" ipos ipos].
    We could then upcast the object. But type U is not syntactic,
    so we can't express this yet using the existing typing
    lemmas.
    And if we use T_New_I on the final type, then [this.A]
    is overly abstract when we try proving that [this.n : this.A];
    see concretely below.
  *)
  Lemma vHasA1': Hs -∗ ⟦ vTyp1 ⟧ ids v.
  Proof.
    iIntros "#Hs".
    iDestruct (T_New_I [] _ with "[]") as "#H"; first last.
    iSpecialize ("H" $! ids with "[#//]").
    rewrite hsubst_id /interp_expr wp_value_inv'.
    iApply "H".
    iApply DCons_I => //.
    - (* Can't finish with D_Typ_Abs, this is only for syntactic types: *)
      (* From D.Dot Require Import typeExtractionSem.
      iApply D_Typ_Abs => //; first last.
      iExists _; iSplit => //=.  (* Here we need a syntactic type matching [ipos]. *) *)
      iModIntro.
      iIntros (ρ Hpid) "/= #_".
      iSplit => //. by iApply sHasA.
    - iApply DCons_I => //; last by iApply DNil_I.
      iApply D_Path_TVMem_I.
      iIntros "!>" (ρ) "/="; iDestruct 1 as "[_ [HA [HB _]]]".
      iDestruct "HA" as (dA) "[HlA HA]".
      iDestruct "HA" as (φ) "[Hlφ HA]".
      iDestruct "HB" as (dB) "[HlB HB]".
      iDestruct "HB" as (w) "HB".
      rewrite !path_wp_pv.
      iExists φ, dA; repeat iSplit => //; try iNext => //.
      (* Last case is stuck, since we don't know what [ρ 0] is and what
      "A" points to. *)
  Abort.

  Lemma wp_prim_step {e : tm} (Hne : to_val e = None) φ :
    WP e {{ φ }} ⊢ ∃ e2, ⌜ prim_step e tt [] e2 tt [] ⌝ ∧ ▷ WP e2 {{ φ }}.
  Proof.
    rewrite wp_unfold/wp_pre/= {}Hne; iIntros "Hwp".
    iDestruct ("Hwp" $! () [] [] 0 with "[//]") as (Hred) "Hwp".
    destruct Hred as (? & e2 & [] & ? & Hr%prim_step_view).
    iDestruct ("Hwp" $! e2 with "[%//]") as "(_ & Heq & _)".
    by iExists _; iFrame.
  Qed.

  Lemma wp_head_step {e : tm} (Hsub : sub_redexes_are_values e) (Hne : to_val e = None) φ :
    WP e {{ φ }} ⊢ ∃ e2 : tm, ⌜ head_step e tt [] e2 tt [] ⌝ ∧ ▷ WP e2 {{ φ }}.
  Proof.
    iIntros "H"; iDestruct (wp_prim_step Hne with "H") as (e2 Hred) "Hwp".
    suff ?: head_step e () [] e2 () [] by iExists _; iFrame.
    destruct Hred as [K]; subst; suff: K = [] by naive_solver.
    by eapply Hsub, val_head_stuck.
  Qed.

  Lemma wp_pos ρ (v : vl) : WP v > 0 {{ w, w ≡ vbool true }} ⊢ ▷ ipos ρ v.
  Proof.
    have Hsub: sub_redexes_are_values (v > 0). {
      apply ectxi_language_sub_redexes_are_values.
      by case => /= *; simplify_eq/=; eauto.
    }
    rewrite /ipos/pos (wp_head_step Hsub) //; iDestruct 1 as (e2 Hhr) "Heq"; iNext.
    have {Hhr}[w [-> Hev]]: ∃ w : vl, e2 = w ∧ bin_op_eval blt 0 v = Some w by inverse Hhr; eauto.
    iDestruct (wp_value_inv' with "Heq") as %->%leibniz_equiv; iIntros "!%".
    (* rewrite wp_value_inv'; iDestruct "Heq" as %->%leibniz_equiv; iIntros "!%". *)
    simpl in Hev; repeat case_match; repeat case_decide; naive_solver.
  Qed.

End ex.

Import dlang_adequacy swap_later_impl.
Lemma vSafe: safe (tv (v 1%positive)).
Proof. eapply (safety_dot_sem dlangΣ)=>*; apply vHasA1TypAd. Qed.
End example.
