From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre.

(** Paolo to Amin: it seems below we might need something vaguely similar to the following. Not sure they're exactly true as stated. *)
Section wp_extra.
Context `{irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(** A variant of wp_wand that requires proof of [Φ v -∗ Ψ v] only if [v] is an evaluation result. *)
Lemma wp_wand_steps s E e Φ Ψ:
    (WP e @ s; E {{ v, Φ v }} -∗
    (** The nsteps premise is wrong for a multithreaded program logic, feel free to use a more accurate one.
        This one might be fine for DOT. *)
    (∀ v σ1 κ σ2 i, ⌜ nsteps i ([e], σ1) κ ([of_val v], σ2) ⌝ -∗ Φ v -∗ Ψ v)-∗
    WP e @ s; E {{ v, Ψ v }})%I.
Admitted.
End wp_extra.

From iris.program_logic Require Import lifting language ectxi_language.
From Dot Require Import tactics unary_lr rules synLemmas.

(** For use with wp_wand_steps; the exact shape of the premise is in question. *)
Lemma steps_preserve_nclosed e v σ1 κ σ2 i n: nsteps i ([e], σ1) κ ([of_val v], σ2) → fv_n e n → fv_n_vl v n.
Admitted.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

Section Sec.
  Context `{HdotG: dotG Σ} Γ.

  Ltac dupGoal := match goal with | |- ?T => assert T as _ end.

  Lemma T_Sub e T1 T2 :
    (Γ ⊨ e : T1 →
    Γ ⊨ [T1, 0] <: [T2, 0] →
    (*───────────────────────────────*)
    Γ ⊨ e : T2)%I.
  Proof.
  (*   iIntros "/= * #[% #HeT1] #Hsub". iSplit; trivial. iIntros " !> * #Hg". *)
  (*   iApply wp_wand. by iApply "HeT1". *)
  (*   iIntros; by iApply "Hsub". *)
  (* Qed. *)
    iIntros "/= * #[% #HeT1] #Hsub". move: H => Hcle. iSplit; trivial; iIntros " !> * #Hg".
    iAssert (⌜ length ρ = length Γ ⌝)%I as "%". by iApply interp_env_len_agree. move: H => Hlen.
    iAssert (⌜ cl_ρ ρ ⌝)%I as "%". by iApply interp_env_closed. move: H => Hclρ.

    set (e' := e.|[to_subst ρ]).

    assert (fv_n e' 0) as Hcleρ.
    { apply fv_to_subst; by rewrite ?Hlen. }

    (* Duplicate goal to show different attempts. *)
    dupGoal.
    dupGoal.
    (** Paolo to Amin: here, it seems we need to show something similar to: if
        [fv_n e' 0] then [WP e' {{v, ⌜ fv_n_vl v 0 ⌝ }}] (where [e' =
        e.|[to_subst ρ]]). (In fact we can't just use that.)

        Maybe using fv_n_vl in interp_expr would shift the proof obligation to a
        better place, but we'd still have to prove something similar.

        More specifically: we know [e]'s result is in [T1] (from ["HeT1"]) and
        must show it's in [T2]. We can almost use ["Hsub"]; but ["Hsub"] only
        says that all *closed* values in T1 are in T2! *)
    - iApply wp_wand.
      by iApply ("HeT1" $! ρ).
      iIntros. iApply "Hsub"; try done.
      admit.
      (** Here we must show tht v is closed, but we can't: in fact [v] is a
          result of evaluating [e'] (in a sense), but [wp_wand] does not expose this fact.

          One possible approach would be to prove [wp_wand_steps], a variant of [wp_wand]
          that exposes the reduction sequence from [e'] to [v], by first proving a variant of
          [wp_strong_mono] that does the same. From the reduction sequence we
          can prove that v is closed outside Iris. See attempt n. 3. *)
    - (** Below, the same problem appears in a different place. *)
      iApply (wp_wand _ _ _ (λ v, ⟦ T1 ⟧ ρ v ∗ ⌜ fv_n_vl v 0 ⌝)%I).
      + iSpecialize ("HeT1" $! ρ with "Hg").
        (**
            This is the situation summarized in
            https://gist.github.com/Blaisorblade/0e928e7b023cfc8bae3b3154a1bd0a90:

            Here we must show [WP e' {{ v, ⟦ T1 ⟧ ρ v ∗ ⌜fv_n_vl v 0⌝ }}] while
            ["HeT1"] only gives [WP e' {{ v, ⟦ T1 ⟧ ρ v }}]. Since [e'] is
            closed, this should be true, but it's hard to prove.
            And I wouldn't know how to fix the hole here;
         *)
        admit.
      + iIntros "* [#H #%]"; by iApply "Hsub".
    (** Attempt n. 3. *)
    - iApply (wp_wand_steps NotStuck ⊤ e' (λ v, ⟦ T1 ⟧ ρ v) (λ v, ⟦ T2 ⟧ ρ v))%I.
      subst e'.
      by iApply ("HeT1" $! ρ).
      iIntros. iApply "Hsub"; try done.
      iPureIntro.
      by eapply steps_preserve_nclosed.
  Admitted.
    (** Paolo to Amin: we can't finish this proof without changing definitions.
        Here we must show that *all values* in TMu T1 are in TMu T2 using
        "Hstp", but "Hstp" only holds for closed values.

        To fix this, we can modify the definition of [Γ ⊨ [T1, i] <: [T2, j]] to
        apply only to closed values, as in next commit. That requires changing
        further definitions in a similar way.

        Alternatively, we could modify [interp] to ensure
        [interp T ρ v → fv_n_vl v 0] and
        [interp T ρ v → fv_n T (length ρ)]
        I think that is a more principled solution, and the one I have used in the past.
     *)

  Lemma T_Var x T:
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ ⊨ tv (var_vl x) : T.|[ren (+x)].
  Proof.
    move => Hx /=; iSplit; first eauto using lookup_fv.
    iIntros "!> * #Hg". iApply wp_value'.
    by iApply interp_env_lookup.
  Qed.

  Lemma Sub_Refl T i : Γ ⊨ [T, i] <: [T, i].
  Proof. by iIntros "/= !> * _" (Hcl) " HT". Qed.

  Lemma Sub_Trans T1 T2 T3 i1 i2 i3 : (Γ ⊨ [T1, i1] <: [T2, i2] →
                                       Γ ⊨ [T2, i2] <: [T3, i3] →
                                       Γ ⊨ [T1, i1] <: [T3, i3])%I.
  Proof.
    iIntros "#Hsub1 #Hsub2 /= !> * #Hg % #HT".
    iApply "Hsub2"; try done. by iApply "Hsub1".
  Qed.

  Lemma Sub_Mono e T i :
    (Γ ⊨ [T, i] <: [T, S i])%I.
  Proof. by iIntros "!> **". Qed.

  Lemma Later_Sub e T i :
    (Γ ⊨ [TLater T, i] <: [T, S i])%I.
  Proof. by iIntros "/= !> ** !>". Qed.

  Lemma Sub_Later e T i :
    (Γ ⊨ [T, S i] <: [TLater T, i])%I.
  Proof. by iIntros "/= !> ** !>". Qed.

  Lemma Sub_Index_Incr e T U i j:
    (Γ ⊨ [T, i] <: [U, j] →
     Γ ⊨ [T, S i] <: [U, S j])%I.
  Proof. iIntros "/= #Hsub !> ** !>". by iApply "Hsub". Qed.

  Lemma T_Skip e T i:
    (Γ ⊨ e : T, S i →
     Γ ⊨ tskip e : T, i)%I.
  Proof.
    iIntros "/= #[% #HT]"; iSplit.
    - iPureIntro; by apply fv_tskip.
    - iIntros " !> * #HG".
      iApply wp_pure_step_later; auto.
      iSpecialize ("HT" $! ρ with "HG"). by iModIntro.
  Qed.

  Lemma And1_Sub T1 T2 i: Γ ⊨ [TAnd T1 T2, i] <: [T1, i].
  Proof. by iIntros "/= !> * ? % [? ?]". Qed.
  Lemma And2_Sub T1 T2 i: Γ ⊨ [TAnd T1 T2, i] <: [T2, i].
  Proof. by iIntros "/= !> * ? % [? ?]". Qed.

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
    iIntros "/= #H1 #H2 !> * #Hg #Hcl #HS".
    iSpecialize ("H1" with "Hg Hcl HS").
    iSpecialize ("H2" with "Hg Hcl HS").
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
  Proof. iIntros "/= #H1 #H2 !> * #Hg #Hcl #[HT1 | HT2]"; by [iApply "H1" | iApply "H2"]. Qed.

  Lemma Sub_Top T i:
    Γ ⊨ [T, i] <: [TTop, i].
  Proof. by iIntros "!> **". Qed.

  Lemma Bot_Sub T i:
    Γ ⊨ [TBot, i] <: [T, i].
  Proof. by iIntros "/= !> ** !>". Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂ᶻ
     ----------------------------------------------- (<:-μ-X)
     Γ ⊨ μ (x: T₁ˣ) <: μ(x: T₂ˣ)
  *)
  (* Notation "◁ n T ▷" := (iterate TLater n T). *)
  Lemma Sub_Mu_X T1 T2 i j:
    (iterate TLater i T1 :: Γ ⊨ [T1, i] <: [T2, j] →
     Γ ⊨ [TMu T1, i] <: [TMu T2, j])%I.
  Proof.
    iIntros "/= #Hstp !> * #Hg #Hcl #HT1".
    iApply ("Hstp" $! (v :: ρ) _);
      rewrite ?iterate_TLater_later //; repeat iSplit; try done.
  Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂
     ----------------------------------------------- (<:-Mu-1)
     Γ ⊨ μ (x: T₁ˣ) <: T₂
  *)

  Lemma Sub_Mu_1 T1 T2 i j:
    (iterate TLater i T1 :: Γ ⊨ [T1, i] <: [T2.|[ren (+1)], j] →
     Γ ⊨ [TMu T1, i] <: [T2, j])%I.
  Proof.
    iIntros "/= #Hstp !> * #Hg #Hcl #HT1".
    iApply (interp_weaken_one v).
    iApply ("Hstp" $! (v :: ρ)); rewrite ?iterate_TLater_later //; repeat iSplit; try done.
  Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ <: T₂ᶻ
     ----------------------------------------------- (<:-Bind-2)
     Γ ⊨ T₁ <: μ(x: T₂ˣ)
  *)
  Lemma Sub_Mu_2 T1 T2 i j:
    (iterate TLater i T1.|[ren (+1)] :: Γ ⊨ [T1.|[ren (+1)], i] <: [T2, j] →
    Γ ⊨ [T1, i] <: [TMu T2, j])%I.
  Proof.
    iIntros "/= #Hstp !> * #Hg #Hcl #HT1".
    rewrite -(interp_weaken_one v T1 ρ v).
    iApply ("Hstp" $! (_ :: _) _); rewrite ?iterate_TLater_later //; repeat iSplit; try done.
  Qed.

  Lemma T_Forall_E e1 e2 T1 T2:
    (Γ ⊨ e1: TAll T1 T2.|[ren (+1)] →
     Γ ⊨ e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
     Γ ⊨ tapp e1 e2 : T2)%I.
  Proof.
    iIntros "/= #[% #He1] #[% #Hv2]". iSplit; eauto using fv_tapp. iIntros " !> * #HG".
    smart_wp_bind (AppLCtx (e2.|[to_subst ρ])) v "#Hv" "He1".
    smart_wp_bind (AppRCtx v) w "#Hw" "Hv2".
    iApply wp_mono; [|iApply "Hv"]; auto.
    iIntros (v0) "#H".
    by iApply (interp_weaken_one w).
  Qed.

  Lemma T_Forall_Ex e1 v2 T1 T2:
    (Γ ⊨ e1: TAll T1 T2 →
     Γ ⊨ tv v2 : T1 →
    (*────────────────────────────────────────────────────────────*)
     Γ ⊨ tapp e1 (tv v2) : T2.|[v2/])%I.
  Proof.
    iIntros "/= #[% #He1] #[% #Hv2Arg]". iSplit; eauto using fv_tapp. iIntros " !> * #HG".
    (* iIntros "/= #He1 #Hv2Arg !> * #HG". *)
    iAssert (⌜ fv_n_vl v2 (length Γ) ⌝)%I as "%". by iPureIntro; apply fv_tv_inv. rename H into Hcl.
    iAssert (⌜ length ρ = length Γ ⌝)%I as "%". by iApply interp_env_len_agree. rename H into Hlen.
    assert (fv_n_vl v2 (length ρ)). by rewrite Hlen.
    smart_wp_bind (AppLCtx (tv v2.[to_subst ρ])) v "#HvFun" "He1".
    iApply wp_wand.
    - iApply fupd_wp.
      iApply "HvFun".
      iApply wp_value_inv'; by iApply "Hv2Arg".
    - iIntros (v0) "#H". by iApply (interp_subst_closed _ T2 v2 v0).
  Qed.

  Lemma T_Forall_I T1 T2 e:
    (T1.|[ren (+1)] :: Γ ⊨ e : T2 →
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2)%I.
  Proof.
    iIntros "/= #[% #HeT]". iSplit. iPureIntro. by apply fv_tv, fv_vabs.
    iIntros " !> * #HG".
    iApply wp_value'.
    iIntros "!>" (v) "#Hv".
    iSpecialize ("HeT" $! (v :: ρ)).
    iApply wp_pure_step_later; trivial.
    asimpl.
    iApply "HeT".
    iFrame "HG".
    iNext. iSplit; first by iApply (interp_weaken_one v).
    (** XXX require argument to be closed in function interpretation. *)
  Admitted.

  Lemma T_Mem_E e T l:
    (Γ ⊨ e : TVMem l T →
    (*─────────────────────────*)
    Γ ⊨ tproj e l : T)%I.
  Proof.
    iIntros "#[% HE] /=". move: H => Hcl.
    iSplit. by iPureIntro; apply fv_tproj.
    iIntros " !>" (ρ) "#HG".
    smart_wp_bind (ProjCtx l) v "#Hv" "HE".
    iDestruct "Hv" as (d) "[% Hv]".
    iDestruct "Hv" as (vmem) "[% Hv]".
    simplOpen ds; subst.
    inversion H; ev; injectHyps.
    iApply wp_pure_step_later; eauto.
    by iApply wp_value'.
  Qed.

  (* BEWARE NONSENSE IN NOTES:
     Γ ⊨ x: Tˣ
     ----------------------------------------------- (<:)
     Γ ⊨ mu(x: Tˣ) <: Tˣ    Γ ⊨ Tˣ <: mu(x: Tˣ)

     Luckily we don't need that, all the rules that exist before appear reasonable. *)

  (*
     Γ ⊨ z: Tᶻ
     =============================================== (T-Rec-I/T-Rec-E)
     Γ ⊨ z: mu(x: Tˣ)
   *)
  Lemma ivstp_rec_eq T v:
    (ivtp Γ (TMu T) v ∗-∗
    ivtp Γ T.|[v/] v)%I.
  Proof.
    (* XXX This is probably a more generally useful combination of closed_subst_vl_id and closed_to_subst. *)
    assert (∀ ρ x, length Γ = length ρ → x < length Γ → cl_ρ ρ →
             to_subst ρ x = (to_subst ρ >> ren (+strings.length ρ)) x) as HtoSubstCl.
    {
      move => ρ x Hleq. rewrite Hleq. move => Hl Hclρ.
      asimpl.
      by rewrite closed_subst_vl_id; [|apply closed_to_subst].
    }
    (* iAssert (□(∀ ρ, ⌜ fv_n_vl v (length ρ) ⌝ → ⌜ cl_ρ ρ ⌝ → *)
    (*              ⟦ T.|[v.[to_subst ρ]/] ⟧ ρ v.[to_subst ρ] ≡ ⟦ T.|[v/] ⟧ ρ v.[to_subst ρ]))%I as "#Hren". *)
    (* { *)
    (*   iIntros "!>" (ρ Hcl Hclρ). *)
    (*   by rewrite -to_subst_interp. *)
    (* } *)
    iSplit; iIntros "/= #[% Htp]"; move: H => Hcl; iSplit; trivial; iIntros " !> * #Hg";
      iSpecialize ("Htp" $! ρ with "Hg");
      (* iSpecialize ("Hren" $! ρ); *)
      iPoseProof (interp_subst ρ T (v.[to_subst ρ]) (v.[to_subst ρ])) as "#Hren1"; asimpl;
      iPoseProof (interp_env_len_agree Γ ρ with "Hg") as "%"; move: H => HlenEq;
      iPoseProof (interp_env_closed Γ ρ with "Hg") as "%"; move: H => Hclρ;
      rewrite - (Hcl (to_subst ρ) ); try naive_solver;
      rewrite -to_subst_interp ?HlenEq; trivial;
      iApply "Hren1"; iApply "Htp".
  Qed.

  (* (* Paolo: This is probably false if we don't assume that v is closed; that *)
  (*    must either follow from the logical relation or be a separate hypothesis. *) *)
  (* Lemma ivstp_rec_eq_alt T v: *)
  (*   ivtp Γ (TMu T) v ≡ *)
  (*   ivtp Γ T.|[v/] v. *)
  (* Proof. *)
  (*   iSplit; iIntros "/= #[% #Htp]"; move: H => Hclv; iSplit; trivial; iIntros " !> * #Hg"; *)
  (*     iSpecialize ("Htp" $! ρ). *)
  (*   - iSpecialize ("Htp" with "Hg"). *)
  (*     rewrite -(interp_subst). asimpl. *)
  (*     admit. *)
  (*   (*   iRewrite "Hren". *) *)
  (*   (*   by iApply "Htp". *) *)
  (*   (* - iRewrite "Hren" in "Htp". *) *)
  (*   (*   by iApply "Htp". *) *)
  (* Admitted. *)

  (*   (* iIntros "#Hclosed". *) *)
  (*   iAssert (□ ∀ ρ, interp_env Γ ρ -∗ interp T.|[v/] ρ v.[to_subst ρ] ∗-∗ interp T (v.[to_subst ρ] :: ρ) v.[to_subst ρ])%I as "#Hren". *)
  (*   (* iAssert (□ ∀ ρ, interp_env Γ ρ -∗ interp T.|[v/] ρ v.[to_subst ρ] ≡ interp T (v :: ρ) v)%I as "#Hren". *) *)
  (*   { *)
  (*     iIntros "!> /= * #Hg". *)
  (*     iPoseProof (interp_subst ρ T (v.[to_subst ρ]) (v.[to_subst ρ])) as "#H". *)
  (*     iSplit; iIntros "#H2". *)
  (*     iApply "H". *)
  (*     asimpl. *)
  (*     rewrite - (Hcl (to_subst ρ) ). *)
  (*     rewrite - (Hcl ids). *)
  (*     rewrite - (Hcl ids (to_subst ρ) ). *)
  (*     asimpl. *)
  (*     iApply "H". *)
  (*   } *)

  (*     (* ("Hclosed" $! (to_subst ρ) ids) as "#H2". *) *)
  (*     (* iRewrite "#H2". *) *)

  (*     (* iPoseProof ("Hclosed" $! (to_subst ρ) ids) as "#H2". *) *)
  (*     (* iRewrite "#H2". *) *)
  (*   iSplit; iIntros "/= #Htp !> * #Hg"; *)
  (*     iSpecialize ("Htp" $! ρ); iSpecialize ("Hren" $! ρ with "Hg"). *)
  (*   -  *)
  (*     iApply "Hren". *)
  (*     by iApply "Htp". *)
  (*   - iApply "Hren". *)
  (*     by iApply "Htp". *)
  (* Qed. *)

  Lemma ivstp_rec_i T v:
    ((∀ ρ1 ρ2, (∀ x, x < length Γ → ρ1 x = ρ2 x) → v.[ρ1] = v.[ρ2]) ->
    ivtp Γ T.|[v/] v -∗
    ivtp Γ (TMu T) v).
  Proof. by intros; iDestruct ivstp_rec_eq as "[? ?]". Qed.

  Lemma ivstp_rec_e T v:
    ((∀ ρ1 ρ2, (∀ x, x < length Γ → ρ1 x = ρ2 x) → v.[ρ1] = v.[ρ2]) ->
    ivtp Γ (TMu T) v -∗
    ivtp Γ T.|[v/] v).
  Proof. by intros; iDestruct ivstp_rec_eq as "[? ?]". Qed.
End Sec.
