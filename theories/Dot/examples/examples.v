From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting adequacy.
From iris.program_logic Require Import ectxi_language.

From D Require Import swap_later_impl.
From D.Dot Require Import scalaLib hoas exampleInfra typingExInfra.

From D.Dot Require Import unary_lr
  lr_lemmas lr_lemmasTSel lr_lemmasNoBinding lr_lemmasDefs lr_lemmasPrim.
From D.Dot Require Import typeExtractionSem.
From D.Dot Require Import skeleton fundamental.

Set Suggest Proof Using.
Set Default Proof Using "Type".

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
Module examples.

Local Hint Constructors bin_op_syntype cond_bin_op_syntype : core.

Tactic Notation "wp_bind" uconstr(p) := iApply (wp_bind (fill [p])).
Ltac wp_bin_base := iApply wp_bin; first eapply cond_bin_op_syntype_sound; by [eauto|].
Ltac wp_bin := iApply wp_wand; [wp_bin_base | iIntros].
Import stamp_transfer.

(* Generic useful lemmas — not needed for fundamental theorem,
    but very useful for examples. *)
Section helpers.
  Context `{HdlangG: dlangG Σ}.

  Lemma alloc {s sγ} φ : sγ !! s = None → allGs sγ ==∗ s ↝n[ 0 ] φ.
  Proof.
    iIntros (Hs) "Hsγ".
    by iMod (leadsto_alloc φ Hs with "Hsγ") as (?) "[_ [_ $]]".
  Qed.
  Lemma wp_ge m n (Hge : m > n) : WP m > n {{ w, w ≡ true }}%I.
  Proof. wp_bin. ev; simplify_eq/=. by case_decide. Qed.
  Lemma wp_nge m n (Hnge : ¬ m > n) : WP m > n {{ w, w ≡ false }}%I.
  Proof. wp_bin. ev; simplify_eq/=. by case_decide. Qed.

  Lemma setp_value Γ (T : olty Σ 0) v: Γ s⊨ tv v : T ⊣⊢ (□∀ ρ, s⟦ Γ ⟧* ρ → T vnil ρ v.[ρ]).
  Proof.
    rewrite /=; properness => //; iSplit;
      [rewrite wp_value_inv|rewrite -wp_value]; iIntros "#$".
  Qed.

  Lemma setp_value_eq (T : olty Σ 0) v: (∀ ρ, T vnil ρ v.[ρ]) ⊣⊢ [] s⊨ tv v : T.
  Proof.
    iSplit.
    - iIntros "#H !>" (? _).
      rewrite /= -wp_value'. iApply "H".
    - iIntros "/= H" (ρ).
      iSpecialize ("H" $! ρ with "[//]").
      by rewrite /= wp_value_inv'.
  Qed.

  Lemma ietp_value_eq T v: (∀ ρ, ⟦ T ⟧ ρ v.[ρ]) ⊣⊢ [] ⊨ tv v : T.
  Proof. apply setp_value_eq. Qed.

  Lemma ietp_value T v: (∀ ρ, ⟦ T ⟧ ρ v.[ρ]) -∗ [] ⊨ tv v : T.
  Proof. by rewrite ietp_value_eq. Qed.

  Lemma ietp_value_inv T v: [] ⊨ tv v : T -∗ ∀ ρ, ⟦ T ⟧ ρ v.[ρ].
  Proof. by rewrite ietp_value_eq. Qed.

  Lemma V_TVMem_I T (v w : vl) l
    (Hclv : nclosed_vl v 0)
    (* XXX should be (Hlook : v @ l ↘ (dpt (pv w))) *)
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
    by rewrite path_wp_pv_eq.
  Qed.
End helpers.

Ltac valMember ρ :=
  iApply V_TVMem_I; [solve_fv_congruence|naive_solver|
    rewrite -ietp_value; iIntros (ρ)].

Local Hint Resolve not_elem_of_nil : core.
Local Hint Constructors NoDup : core.

Section s_is_pos.

Context `{HdlangG: dlangG Σ}.
Context (s: stamp).

Definition pos v := ∃ n, v = vnat n ∧ n > 0.
Definition ipos: oltyO Σ 0 := olty0 (λI ρ v, ⌜ pos v ⌝).

Definition Hs := (s ↝n[ 0 ] ipos)%I.
Lemma allocHs sγ:
  sγ !! s = None → allGs sγ ==∗ Hs.
Proof. exact (alloc ipos). Qed.

Section div_example.
  Lemma idtp_value_eq T l d (Hl : label_of_ty T = Some l):
    (∀ ρ, ⌜path_includes (pv (ids 0)) ρ [(l, d)]⌝ → D*⟦ T ⟧ ρ d.|[ρ]) ⊣⊢ [] s⊨ { l := d } : C⟦ T ⟧.
  Proof.
    rewrite /idtp/=/lift_ldlty/= ld_label_match Hl; iSplit.
    by iIntros "#H !> /=" (ρ Hpid _); iSplit; first done; iApply "H".
    by iIntros "#H" (ρ Hpid); iDestruct ("H" $! ρ Hpid with "[//]") as "[_ $]".
  Qed.

  (* Arguments dlang_ectx_lang : simpl never.
  Arguments dlang_ectxi_lang : simpl never. *)

  Lemma pos_wp ρ v : ipos vnil ρ v ⊢ WP v > 0 {{ w, w ≡ vbool true }}.
  Proof. iDestruct 1 as %(n & -> & ?). by iApply wp_ge. Qed.

  Context `{SwapPropI Σ}.
  Lemma loopSemT: WP hclose hloopTm {{ _, False }}%I.
  Proof using Type*.
    iDestruct (fundamental_typed _ _ _ _ (loopTyp []) with "[]") as "H".
    iApply wellMappedφ_empty.
    iSpecialize ("H" $! ids with "[//]").
    by rewrite hsubst_id /=.
  Qed.

  Definition hmkPosBodyV n := htif (n > 0) n hloopTm.
  Definition hmkPosV := λ: n, hmkPosBodyV n.

  Lemma wp_if_ge (n : nat) :
    WP hclose (hmkPosBodyV n) {{ w, ⌜ w = n ∧ n > 0 ⌝}}%I.
  Proof using Type*.
    wp_bind (IfCtx _ _).
    wp_bin; ev; simplify_eq/=.
    case_decide; rewrite -wp_pure_step_later //; iNext.
    by rewrite -wp_value'.
    iApply wp_wand; [iApply loopSemT | naive_solver].
  Qed.

  Lemma wp_if_ge' (n : nat) :
    WP tif (n > 0) (1 `div` n) (hclose hloopTm) {{ w, ⟦ 𝐍 ⟧ ids w ∧ ⌜ n > 0 ⌝}}%I.
  Proof using Type*.
    wp_bind (IfCtx _ _).
    wp_bin; ev; simplify_eq/=.
    case_decide; rewrite -wp_pure_step_later //; iNext.
    - wp_bin. naive_solver.
    - iApply wp_wand; [iApply loopSemT | naive_solver].
  Qed.

  (* Experiments using fancier infrastructure: *)
  Lemma allocHsGen sγ:
    sγ !! s = None → allGs sγ ==∗ Hs.
  Proof.
    (* iIntros (Hl) "H". iApply wellMappedφ_apply.
    Fail pose (t := transfer (<[s:=ipos]> ∅)).
    pose (u := transfer (<[s:=olty_car ipos]> ∅)).
    2: iApply (transfer (<[s:=ipos]> ∅) with "H") => s'.
      Unshelve. 3: apply _.
    (* Check transfer (<[s:=olty_car ipos]> ∅). *)
    Fail pose (t := transfer (<[s:=ipos]> ∅)). *)

    iIntros (Hl) "H". iApply wellMappedφ_apply;
      last iApply (transfer (<[s:=olty_car ipos]> ∅) with "H") => s';
      rewrite ?lookup_insert ?dom_insert ?dom_empty //; set_solver+ Hl.
  Qed.

  Lemma allocHs1: allGs ∅ ==∗ Hs.
  Proof.
    iIntros "H"; iApply wellMappedφ_apply; last iApply (transfer_empty (<[s:=olty_car ipos]> ∅) with "H").
    by rewrite lookup_insert.
  Qed.

  Import hoasNotation.

  Definition posModT := μ: self, {@
    type "Pos" >: ⊥ <: 𝐍;
    val "mkPos" : 𝐍 →: self @; "Pos";
    val "div" : 𝐍 →: self @; "Pos" →: 𝐍
  }.

  Definition hdivV := λ: m n, (htskip m) `div` n.

  (** We assume [Hs] throughout the rest of the section. *)
  Import DBNotation.

  Definition posModV := ν {@
    type "Pos" = ([]; s);
    val "mkPos" = pv (hclose hmkPosV);
    val "div" = pv (hclose hdivV)
  }.

  Lemma sToIpos : Hs -∗ dtysem [] s ↗n[ 0 ] hoEnvD_inst [] ipos.
  Proof. by iApply dm_to_type_intro. Qed.

  Lemma Sub_ipos_nat Γ : Γ s⊨ ipos, 0 <: V⟦ 𝐍 ⟧, 0.
  Proof.
    rewrite /ipos /pos /= /pure_interp_prim /prim_evals_to /=.
    iIntros "!>" (ρ w) "_ % !%"; naive_solver.
  Qed.

  Lemma Sub_later_ipos_nat Γ : Γ s⊨ oLater ipos, 0 <: oLater V⟦ 𝐍 ⟧, 0.
  Proof. rewrite -sSub_Later_Sub -sSub_Index_Incr. apply Sub_ipos_nat. Qed.

  Lemma sHasA' l Γ : Hs -∗ Γ s⊨ { l := dtysem [] s } : C⟦ type l >: ⊥ <: 𝐍 ⟧.
  Proof.
    iIntros "Hs".
    iApply (sD_Typ_Abs ipos); [|iApply sBot_Sub|by iExists _; iFrame "Hs"].
    iApply Sub_later_ipos_nat.
  Qed.
  Definition testVl l : vl := ν {@ type l = ([]; s)}.

  Lemma sInTestVl l ρ :
    path_includes (pv (ids 0)) (testVl l .: ρ) [type l = ([]; s)].
  Proof. constructor; naive_solver. Qed.
  Hint Resolve sInTestVl : core.

  Lemma sHasA l : Hs -∗ D*⟦ type l >: ⊥ <: 𝐍 ⟧ ids (dtysem [] s).
  Proof.
    rewrite (sHasA' l []); iIntros "H".
    by iDestruct ("H" $! (testVl l .: ids) with "[] []") as "[_ $]".
  Qed.

  Lemma posModVHasAtyp: Hs -∗ [] ⊨ posModV : type "Pos" >: ⊥ <: TNat.
  Proof.
    rewrite -ietp_value; iIntros "#Hs" (ρ).
    iExists _; iSplit; by [eauto | iApply (sHasA "Pos")].
  Qed.

  Lemma ty_mkPos :
    [] s⊨ hclose hmkPosV : oAll V⟦ 𝐍 ⟧ (olty0 (λI ρ v, ⌜ ∃ n : nat, v = n ∧ n > 0 ⌝)).
  Proof using Type*.
    rewrite -sT_All_I /= /shead.
    iIntros (ρ) "!> /=". iDestruct 1 as %(_ & n & Hw); simplify_eq/=; rewrite Hw.
    iIntros "!>". iApply wp_wand; [iApply wp_if_ge | naive_solver].
  Qed.

  Lemma wp_mkPos :
    oAll V⟦ 𝐍 ⟧ (olty0 (λI ρ v, ⌜ ∃ n : nat, v = n ∧ n > 0 ⌝)) vnil ids (hclose hmkPosV).
  Proof using Type*. iApply wp_value_inv'. iApply (ty_mkPos with "[//]"). Qed.

  Lemma wp_div_spec (m : nat) w : ipos vnil ids w -∗ WP m `div` w {{ ⟦ 𝐍 ⟧ ids }}.
  Proof. iDestruct 1 as %(n&?&?); simplify_eq. wp_bin. by iIntros "!%"; naive_solver. Qed.

  Lemma posModVHasA: Hs -∗ [] ⊨ posModV : hclose posModT.
  Proof using Type*.
    rewrite /posModT -(T_Mu_I _ posModV).
    iIntros "#Hs /=".
    iApply sT_And_I; first by iApply posModVHasAtyp.
    iApply sT_And_I; last iApply sT_And_I; last by
      iIntros "!> ** /="; rewrite -wp_value'.
    - valMember ρ; iExists _; iSplit; [done|].
      iIntros (w) "!>"; iMod 1 as %[n Hw]; iIntros "!> !>".
      simplify_eq/=.
      iApply wp_wand; [iApply wp_if_ge | iIntros "/=" (v [-> ?])].
      rewrite path_wp_pv_eq.
      repeat (iExists _; try iSplit => //=).
      iSplit => //. by iApply dm_to_type_intro.
      iIntros "!%"; rewrite /pos.
      naive_solver.
    - valMember ρ; iExists _; iSplit; [done|].
      iIntros (v) "!>"; iMod 1 as %[m Hw]; iIntros "!> !>".
      rewrite -wp_value'; simplify_eq/=; iExists _; iSplit; [done|].
      iIntros (w) "!> #Harg!>!>"; rewrite path_wp_pv_eq /=.
      iDestruct "Harg" as (Φ d [ds Hlook]) "[Hs1 #Harg]";
        have {d ds Hlook}->: d = dtysem [] s by naive_solver.
      iPoseProof (sToIpos with "Hs") as "Hs2/=".
      iPoseProof (dm_to_type_agree vnil w with "Hs1 Hs2") as "{Hs Hs1 Hs2} Heq".
      wp_bind (BinLCtx _ _); rewrite -wp_pure_step_later // -wp_value/=/lang.of_val.
      iNext. iRewrite "Heq" in "Harg"; iClear "Heq".
      by iApply wp_div_spec.
  Qed.
End div_example.

Section wp_inv.
  Import ectxi_language ectx_language.

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

  Lemma wp_pos ρ (v : vl) : WP v > 0 {{ w, w ≡ vbool true }} ⊢ ▷ ipos vnil ρ v.
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

End wp_inv.

Section small_ex.
  (* Generic useful lemmas — not needed for fundamental theorem,
     but very useful for examples. *)

  (** Under Iris assumption [Hs], [v.A] points to [ipos]. *)
  Import DBNotation.

  Definition v := ν {@
    type "A" = ([]; s);
    val "n" = pv (vnat 2)
  }.

  Definition vTyp1Body : ty := {@
    type "A" >: ⊥ <: 𝐍;
    val "n" : p0 @; "A"
  }.
  Definition vTyp1 := μ vTyp1Body.


  (** Yes, v has a valid type member. *)
  Lemma vHasA0typ: Hs -∗ [] ⊨ tv v : type "A" >: ⊥ <: 𝐍.
  Proof.
    iIntros "#Hs".
    iApply (T_Sub (i := 0) (T1 := μ {@ type "A" >: ⊥ <: 𝐍})).
    iApply T_Obj_I.
    iApply D_Cons; [done| by iApply sHasA'|].
    iSplit; [iIntros "!%"|iIntros "!> ** //"].
    repeat constructor; exact: not_elem_of_nil.
    iApply Sub_Trans.
    iApply (Sub_Mu_A {@ type "A" >: ⊥ <: 𝐍}).
    iApply sAnd1_Sub.
  Qed.
  (* This works. Crucially, we use T_Mu_I to introduce the object type.
     This way, we can inline the object in the type selection.
     This cannot be done using T_Obj_I directly.
     However, this is closer to how typechecking in Scala
     actually works.
     XXX: also, maybe this *could* be done with T_Obj_I with
     a precise type? That'd be a more correct derivation.
   *)
  (* Lemma vHasA1: Hs -∗ ∀ ρ, ⟦ vTyp1 ⟧ ρ v.[ρ]. *)
  Lemma vHasA1t : Hs -∗ [] ⊨ tv v : vTyp1.
  Proof.
    rewrite -(T_Mu_I _ v).
    iIntros "#Hs /=".
    iApply sT_And_I; first by [iApply vHasA0typ].
    iApply sT_And_I; first last.
    - iApply (T_Sub (i := 0) (T2 := TTop)); last by iApply sSub_Top.
      by iApply vHasA0typ.
    - rewrite -setp_value_eq /= /iPPred_car /=.
      have Hev2: pos (vnat 2) by rewrite /pos; eauto.
      iIntros (_).

      repeat (repeat iExists _; repeat iSplit; rewrite ?path_wp_pv_eq //);
        try by [|iApply dm_to_type_intro].
  Qed.

  (*
    A different approach would be to type the object using T_Obj_I
    with an object type [U] with member [TTMem "A" ipos ipos].
    We could then upcast the object. But type U is not syntactic,
    so we can't express this yet using the existing typing
    lemmas.
    And if we use T_Obj_I on the final type, then [this.A]
    is overly abstract when we try proving that [this.n : this.A];
    see concretely below.
  *)
  Definition vTyp2Body : ty := {@
    type "A" >: ⊥ <: 𝐍;
    val "n" : TLater (p0 @; "A")
  }.
  Definition vTyp2 := μ vTyp2Body.

  Definition svTyp2Body : oltyO Σ 0 :=
    oAnd (cTMem "A" oBot (oPrim tnat))
      (oAnd (cVMem "n" (oLater (oSel p0 "A")))
      oTop).
  Goal V⟦vTyp2Body⟧ = svTyp2Body. done. Abort.
  Definition svTyp2 := oMu svTyp2Body.

  Definition svTyp2ConcrBody : cltyO Σ :=
    cAnd (cTMem "A" ipos ipos)
      (cAnd (cVMem "n" (oLater (oSel p0 "A")))
      cTop).
  Definition svTyp2Concr := oMu svTyp2ConcrBody.

  Lemma sT_Var0 {Γ T}
    (Hx : Γ !! 0 = Some T):
    (*──────────────────────*)
    Γ s⊨ of_val (ids 0) : T.
  Proof. rewrite -(hsubst_id T). apply (sT_Var Hx). Qed.

  (* This works! But we get a weaker type, because we're using typing rules
  for recursive objects on a not-really-recursive one. *)
  Lemma vHasA2t `{SwapPropI Σ}: Hs -∗ [] s⊨ tv v : svTyp2.
  Proof.
    iIntros "#Hs".
    iApply (sT_Sub (i := 0) (T1 := svTyp2Concr)); first last.
    - iApply sSub_Mu_X; rewrite /svTyp2ConcrBody /vTyp1Body iterate_0.
      iApply sSub_And; last iApply sSub_And; last iApply sSub_Top.
    + iApply sSub_Trans; first iApply sAnd1_Sub.
      iApply sTyp_Sub_Typ; [iApply sBot_Sub | iApply Sub_later_ipos_nat].
    + iApply sSub_Trans; first iApply sAnd2_Sub.
      iApply sAnd1_Sub.
    - rewrite /v /svTyp2Concr /svTyp2ConcrBody.
      iApply sT_Obj_I.
      iApply sD_Cons; first done.
      iApply (sD_Typ_Abs ipos); [iApply sSub_Refl..|by iExists _; iFrame "Hs"].
      iApply sD_Cons; [done| |iApply sD_Nil].
      iApply sD_TVMem_I.
      iApply (sT_Sub (i := 0) (T1 := ipos)).
      rewrite setp_value /ipos /pos; iIntros "!>" (ρ) "_ /= !%". naive_solver.
      iApply sSub_Trans; first iApply sSub_Add_Later.
      iApply sSub_Trans; first iApply sSub_Add_Later.
      iApply sSub_Later_Sub.
      iApply sSub_Sel_Path.
      iApply sP_Later.
      iApply sP_Val.
      iApply (sT_Sub (i := 0)).
      by iApply sT_Var0.
      iApply sSub_Later_Sub.
      iApply sAnd1_Sub.
  Qed.

  Lemma vHasA1': Hs -∗ ⟦ vTyp1 ⟧ ids v.
  Proof.
    iIntros "#Hs".
    iDestruct (T_Obj_I [] vTyp1Body with "[]") as "#H"; first last.
    iSpecialize ("H" $! ids with "[#//]").
    rewrite hsubst_id /interp_expr wp_value_inv'.
    iApply "H".
    iApply D_Cons => //.
    - (* Can't finish with D_Typ_Abs, this is only for syntactic types: *)
      (* From D.Dot Require Import typeExtractionSem.
      iApply sD_Typ_Abs => //; first last.
      iExists _; iSplit => //=.  (* Here we need a syntactic type matching [ipos]. *) *)
      iModIntro.
      iIntros (ρ Hpid) "/= #_".
      iSplit => //. by iApply sHasA.
    - iApply D_Cons => //; last by iApply D_Nil.
      iApply D_Path_TVMem_I.
      iIntros "!>" (ρ) "/="; iDestruct 1 as "[_ [HA [HB _]]]".
      iDestruct "HA" as (dA) "[HlA HA]".
      iDestruct "HA" as (φ) "[Hlφ HA]".
      iDestruct "HB" as (dB) "[HlB HB]".
      iDestruct "HB" as (w) "HB".
      rewrite !path_wp_pv_eq.
      iExists φ, dA; repeat iSplit => //; try iNext => //.
      (* Last case is stuck, since we don't know what [ρ 0] is and what
      "A" points to. *)
  Abort.
End small_ex.
End s_is_pos.

Import dlang_adequacy swap_later_impl.
Lemma vSafe: safe (tv (v 1%positive)).
Proof.
  eapply (safety_dot_sem dlangΣ (T := vTyp1))=>*.
  by rewrite (allocHs 1%positive) // -vHasA1t.
Qed.

End examples.
