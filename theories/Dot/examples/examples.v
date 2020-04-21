From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting adequacy.
From iris.program_logic Require Import ectxi_language.

From D Require Import swap_later_impl.
From D.Dot Require Import scalaLib hoas exampleInfra typingExInfra.

From D.Dot Require Import unary_lr
  lr_lemmas lr_lemmasTSel lr_lemmasNoBinding lr_lemmasDefs lr_lemmasPrim.
From D.Dot Require Import typeExtractionSem.
From D.Dot Require Import skeleton fundamental.
Import dlang_adequacy.

Set Suggest Proof Using.
Set Default Proof Using "Type".

Implicit Types (v w : vl) (d : dm) (ds : dms).

Import hoas.syn.

(* XXX move into hoas.v. *)
Module hoasNotation'.
  Export hoasNotation.
  Notation "'type' l = ( σ ; s )" := (l, hdtysem σ s) (at level 60, l at level 50).
End hoasNotation'.

Module Import examplesBodies.
Import hoasNotation'.

Definition posModT := μ: self, {@
  type "Pos" >: ⊥ <: 𝐙;
  val "mkPos" : 𝐙 →: self @; "Pos";
  val "div" : 𝐙 →: self @; "Pos" →: 𝐙
}.

Definition hdivV := λ: m n, m `div` (htskip n).
Definition hmkPosBodyV (n : hvl) := htif (n > 0) n hloopTm.
Definition hmkPosV := λ: n, hmkPosBodyV n.

Definition hposModV s : hvl := ν: _ , {@
  type "Pos" = ([]; s);
  val "mkPos" = hmkPosV;
  val "div" = hdivV
}.

Definition hminiV s := ν: _, {@
  type "A" = ([]; s);
  val "n" = 2
}.

End examplesBodies.

Example loopDefTyp Γ : Γ v⊢ₜ[ ∅ ] hloopDefV : hloopDefT.
Proof.
  apply (iT_Sub_nocoerce hloopDefTConcr); mltcrush.
  eapply iT_All_E; last var.
  tcrush; varsub; lookup.
Qed.

Example loopFunTyp Γ : Γ v⊢ₜ[∅] hloopFunTm : ⊤ →: ⊥.
Proof. have ? := loopDefTyp Γ; tcrush. Qed.

Example loopTyp Γ : Γ v⊢ₜ[∅] hloopTm : ⊥.
Proof.
  have ? := loopFunTyp Γ; apply (iT_All_E (T1 := ⊤)), (iT_Sub_nocoerce 𝐙); tcrush.
Qed.

Module examples.

Local Hint Constructors bin_op_syntype cond_bin_op_syntype : core.
Local Hint Extern 1000 => lia : core.

Tactic Notation "wp_bind" uconstr(p) := iApply (wp_bind (fill [p])).
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

  Lemma setp_value Γ (T : olty Σ 0) v: Γ s⊨ v : T ⊣⊢ (□∀ ρ, s⟦ Γ ⟧* ρ → T vnil ρ v.[ρ]).
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
    (* XXX should be (Hlook : v @ l ↘ (dpt (pv w))) *)
    (Hlook : objLookup v l (dpt (pv w))):
    [] ⊨ w : T -∗
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

Context `{HdlangG: !dlangG Σ}.
Context (s: stamp).

Definition pos v := ∃ n, v = vint n ∧ n > 0.
Definition ipos: oltyO Σ 0 := olty0 (λI ρ v, ⌜ pos v ⌝).

Definition Hs : iProp Σ := s ↝n[ 0 ] ipos.
Lemma allocHs sγ:
  sγ !! s = None → allGs sγ ==∗ Hs.
Proof. exact (alloc ipos). Qed.

Section div_example.
  Lemma idtp_value_eq T l d (Hl : label_of_ty T = Some l):
    (∀ ρ, ⌜path_includes x0 ρ [(l, d)]⌝ → D*⟦ T ⟧ ρ d.|[ρ]) ⊣⊢ [] s⊨ { l := d } : C⟦ T ⟧.
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
  Lemma loopSemT: ⊢ WP hloopTm {{ _, False }}.
  Proof using Type*.
    iDestruct (fundamental_typed (loopTyp []) with "[]") as "H".
    iApply wellMappedφ_empty.
    iSpecialize ("H" $! ids with "[//]").
    by rewrite hsubst_id /=.
  Qed.

  Section useHoas.
  Import hoasNotation'.
  Lemma wp_if_ge (n : Z) :
    ⊢ WP hmkPosBodyV n {{ w, ⌜ w = n ∧ n > 0 ⌝}}.
  Proof using Type*.
    wp_bind (IfCtx _ _).
    wp_bin; ev; simplify_eq/=.
    case_decide; rewrite -wp_pure_step_later //; iNext.
    by rewrite -wp_value'; auto.
    iApply wp_wand; [iApply loopSemT | naive_solver].
  Qed.

  Lemma wp_if_ge' (n : Z) :
    ⊢ WP tif (n > 0) (1 `div` n) hloopTm {{ w, ⟦ 𝐙 ⟧ ids w ∧ ⌜ n > 0 ⌝}}.
  Proof using Type*.
    wp_bind (IfCtx _ _).
    wp_bin; ev; simplify_eq/=.
    case_decide; rewrite -wp_pure_step_later //; iNext.
    - wp_bin. naive_solver.
    - iApply wp_wand; [iApply loopSemT | naive_solver].
  Qed.
  End useHoas.

  (** We assume [Hs] throughout the rest of the section. *)

  Definition posModV : vl := hposModV s.

  Lemma sToIpos : Hs -∗ dtysem [] s ↗n[ 0 ] hoEnvD_inst [] ipos.
  Proof. by iApply dm_to_type_intro. Qed.

  Lemma Sub_ipos_nat Γ : ⊢ Γ s⊨ ipos, 0 <: V⟦ 𝐙 ⟧, 0.
  Proof.
    rewrite /ipos /pos /= /pure_interp_prim /prim_evals_to /=.
    iIntros "!>" (ρ w) "_ % !%"; naive_solver.
  Qed.

  Lemma Sub_later_ipos_nat Γ : ⊢ Γ s⊨ oLater ipos, 0 <: oLater V⟦ 𝐙 ⟧, 0.
  Proof. rewrite -sSub_Later_Sub -sSub_Index_Incr. apply Sub_ipos_nat. Qed.

  Lemma sHasA' l Γ : Hs -∗ Γ s⊨ { l := dtysem [] s } : C⟦ type l >: ⊥ <: 𝐙 ⟧.
  Proof.
    iIntros "Hs".
    iApply (sD_Typ_Abs ipos); [|iApply sBot_Sub|by iExists _; iFrame "Hs"].
    iApply Sub_later_ipos_nat.
  Qed.

  Definition testDm := dtysem [] s.
  Definition testVl l : vl := ν {@ (l, testDm) }.

  Lemma sInTestVl l ρ :
    path_includes (pv x0) (testVl l .: ρ) [(l, testDm)].
  Proof. constructor; naive_solver. Qed.

  Lemma sHasA l : Hs -∗ D*⟦ type l >: ⊥ <: 𝐙 ⟧ ids testDm.
  Proof.
    rewrite (sHasA' l []); iIntros "H".
    iDestruct ("H" $! (testVl l .: ids) with "[] []") as "[_ $]"; auto using sInTestVl.
  Qed.

  Lemma posModVHasATy: Hs -∗ [] ⊨ posModV : type "Pos" >: ⊥ <: TInt.
  Proof.
    rewrite -ietp_value; iIntros "#Hs" (ρ).
    iExists _; iSplit; by [eauto | iApply (sHasA "Pos")].
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
    iApply sT_And_I; first by iApply posModVHasATy.
    iApply sT_And_I; last iApply sT_And_I; last by
      iIntros "!> ** /="; rewrite -wp_value'.
    - iApply V_TVMem_I; [solve_fv_congruence|naive_solver|].
      iApply sT_All_I.
      rewrite /= /shead.
      iIntros "!>" (ρ [_ [n Hw]]) "!> /=".
      simplify_eq/=; rewrite Hw.
      iApply wp_wand; [iApply wp_if_ge |iIntros "/=" (v [-> ?])].
      rewrite path_wp_pv_eq.
      repeat (iExists _; try iSplit => //=).
      iSplit => //. by iApply dm_to_type_intro.
      iIntros "!%"; rewrite /pos.
      naive_solver.
    - iApply V_TVMem_I; [solve_fv_congruence|naive_solver|].
      iApply sT_All_I.
      iApply sT_All_I.
      rewrite /= /shead /stail/=.
      iIntros "!>" (ρ ) "#[[_ Hw] Harg] !> /=".
      iDestruct "Hw" as %[m ->].
      setoid_rewrite path_wp_pv_eq.
      setoid_rewrite later_intuitionistically.
      iDestruct "Harg" as (Φ d [ds Hlook]) "[Hs1 #Harg]";
        have {d ds Hlook}->: d = dtysem [] s by naive_solver.
      iPoseProof (sToIpos with "Hs") as "Hs2/=".
      iPoseProof (dm_to_type_agree vnil (ρ 0) with "Hs1 Hs2") as "{Hs Hs1 Hs2} Heq".
      wp_bind (BinRCtx _ _); rewrite -wp_pure_step_later // -wp_value/=/lang.of_val.
      iNext. iRewrite "Heq" in "Harg"; iClear "Heq".
      by iApply wp_div_spec.
  Qed.
End div_example.

Section small_ex.
  (* Generic useful lemmas — not needed for fundamental theorem,
     but very useful for examples. *)

  (** Under Iris assumption [Hs], [miniV.A] points to [ipos]. *)
  Import DBNotation.

  Definition miniVT1Body : ty := {@
    type "A" >: ⊥ <: 𝐙;
    val "n" : p0 @; "A"
  }.
  Definition miniVT1 := μ miniVT1Body.
  Definition miniV : vl := hminiV s.


  (** Yes, miniV has a valid type member. *)
  Lemma vHasA0typ: Hs -∗ [] ⊨ miniV : type "A" >: ⊥ <: 𝐙.
  Proof.
    iIntros "#Hs".
    iApply (T_Sub (i := 0) (T1 := μ {@ type "A" >: ⊥ <: 𝐙})).
    iApply T_Obj_I.
    iApply D_Cons; [done| by iApply sHasA'|].
    iSplit; [iIntros "!%"|iIntros "!> ** //"].
    repeat constructor; exact: not_elem_of_nil.
    iApply Sub_Trans.
    iApply (Mu_Sub {@ type "A" >: ⊥ <: 𝐙}).
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
  Lemma vHasA1t : Hs -∗ [] ⊨ miniV : miniVT1.
  Proof.
    rewrite -(T_Mu_I _ miniV).
    iIntros "#Hs /=".
    iApply sT_And_I; first by [iApply vHasA0typ].
    iApply sT_And_I; first last.
    - iApply (T_Sub (i := 0) (T2 := TTop)); last by iApply sSub_Top.
      by iApply vHasA0typ.
    - rewrite -setp_value_eq /= /iPPred_car /=.
      have Hev2: pos (vint 2) by rewrite /pos; eauto.
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
  Definition miniVT2Body : ty := {@
    type "A" >: ⊥ <: 𝐙;
    val "n" : TLater (p0 @; "A")
  }.
  Definition miniVT2 := μ miniVT2Body.

  Definition sminiVT2Body : oltyO Σ 0 :=
    oAnd (cTMem "A" oBot (oPrim tint))
      (oAnd (cVMem "n" (oLater (oSel p0 "A")))
      oTop).
  Goal V⟦miniVT2Body⟧ = sminiVT2Body. done. Abort.
  Definition sminiVT2 := oMu sminiVT2Body.

  Definition sminiVT2ConcrBody : cltyO Σ :=
    cAnd (cTMem "A" ipos ipos)
      (cAnd (cVMem "n" (oLater (oSel p0 "A")))
      cTop).
  Definition sminiVT2Concr := oMu sminiVT2ConcrBody.

  Lemma sT_Var0 {Γ T}
    (Hx : Γ !! 0%nat = Some T):
    (*──────────────────────*)
    ⊢ Γ s⊨ x0 : T.
  Proof. rewrite -(hsubst_id T). apply (sT_Var Hx). Qed.

  (* This works! But we get a weaker type, because we're using typing rules
  for recursive objects on a not-really-recursive one. *)
  Lemma vHasA2t `{SwapPropI Σ}: Hs -∗ [] s⊨ miniV : sminiVT2.
  Proof.
    iIntros "#Hs".
    iApply (sT_Sub (i := 0) (T1 := sminiVT2Concr)); first last.
    - iApply sMu_Sub_Mu; rewrite /sminiVT2ConcrBody /miniVT1Body oLaterN_0.
      iApply sSub_And; last iApply sSub_And; last iApply sSub_Top.
    + iApply sSub_Trans; first iApply sAnd1_Sub.
      iApply sTyp_Sub_Typ; [iApply sBot_Sub | iApply Sub_later_ipos_nat].
    + iApply sSub_Trans; first iApply sAnd2_Sub.
      iApply sAnd1_Sub.
    - rewrite /miniV /sminiVT2Concr /sminiVT2ConcrBody.
      iApply sT_Obj_I.
      iApply sD_Cons; first done.
      iApply (sD_Typ_Abs ipos); [iApply sSub_Refl..|by iExists _; iFrame "Hs"].
      iApply sD_Cons; [done| |iApply sD_Nil].
      iApply sD_Val.
      iApply (sT_Sub (i := 0) (T1 := ipos)).
      rewrite setp_value /ipos /pos; iIntros "!>" (ρ) "_ /= !%". naive_solver.
      iApply sSub_Trans; first iApply sSub_Add_Later.
      iApply sSub_Trans; first iApply sSub_Add_Later.
      iApply sSub_Later_Sub.
      iApply sSub_Sel.
      iApply sP_Later.
      iApply sP_Val.
      iApply (sT_Sub (i := 0)).
      by iApply sT_Var0.
      iApply sSub_Later_Sub.
      iApply sAnd1_Sub.
  Qed.
End small_ex.
End s_is_pos.

Lemma miniVSafe (s : stamp): safe (miniV s).
Proof.
  eapply (safety_dot_sem dlangΣ (T := miniVT1))=>*.
  by rewrite (allocHs s) // -vHasA1t.
Qed.

Lemma posModVSafe (s : stamp): safe (posModV s).
Proof.
  eapply (safety_dot_sem dlangΣ (T := posModT))=>*.
  by rewrite (allocHs s) // -posModTy.
Qed.

End examples.
