(** * Demonstrate semantic typing rules for applicative, syntactic type members.
That is, these are type definitions that:
- contain syntactic types (which avoid the need for stamping).
- are interpreted using our logical relation
- therefore, can be robustly given "applicative"-like semantics (as in storeless
DOT in Amin's thesis).

We can _almost_ get the rules of storeless DOT (and applicative semantics) even)
even without syntactic type members, but not quite; stamping the same type twice
will produce different stamps, ensuring generative semantics.
*)

From iris.proofmode Require Import tactics.
From D Require Import iris_prelude.
From D.Dot Require Import dot_lty dot_semtypes hkdot unary_lr.
From D.Dot Require Import defs_lr binding_lr dsub_lr path_repl_lr sub_lr examples_lr.
From D.Dot Require Import hoas ex_utils.
From D.Dot Require Import sem_unstamped_typing.
(* From D.Dot Require Import binding_lr_syn dsub_lr_syn path_repl_lr_syn sub_lr_syn
  examples_lr_syn sem_unstamped_typing. *)

Import SKindSyn HkDot.

Section lemmas.
  Context `{Hdlang : !dlangG Σ} `{HswapProp : SwapPropI Σ}.

  (* XXX upstream. *)
  #[global] Arguments dot_rec_ty_interp {_ _} /.

  (* XXX can't upstream. *)
  Transparent dm_to_type.
  Lemma dm_to_type_syn_intro' d T ρ :
    d = dtysyn T.|[ρ] → ⊢ d ↗ (λ args, V⟦ T ⟧ args ρ).
  Proof. move->. iIntros "/= !> % !% %v". apply (interp_subst_ids T ρ). Qed.
  Opaque dm_to_type.

  Lemma sD_TypK_Abs_Syn {l Γ} T (K : sf_kind Σ) :
    Γ s⊨ oLater V⟦ T ⟧ ∷[ 0 ] K -∗
    Γ s⊨ { l := dtysyn T } : cTMemK l K.
  Proof.
    rewrite sdtp_eq'. pupd; iIntros "#HTK !>" (ρ Hpid) "Hg /=".
    iExists (λ args, V⟦ T ⟧ args ρ).
    iDestruct (dm_to_type_syn_intro') as "-#$"; first done.
    iApply (sfkind_respects with "[] (HTK Hg)").
    iIntros "%%".
    by iSplit; iIntros "$".
  Qed.

  Lemma sD_Typ_Syn {l Γ T} :
    ⊢ Γ s⊨ { l := dtysyn T } : cTMem l (oLater V⟦ T ⟧) (oLater V⟦ T ⟧).
  Proof.
    iApply sD_TypK_Abs_Syn.
    (* Many lemma permutations are possible here. *)
    iApply sK_Sing_deriv.
  Qed.

  Lemma suD_Typ_Syn {l Γ T} :
    ⊢ Γ su⊨ { l := dtysyn T } : cTMem l (oLater V⟦ T ⟧) (oLater V⟦ T ⟧).
  Proof.
    pupd; iModIntro. iExists (dtysyn T); iSplit; first done. iApply sD_Typ_Syn.
  Qed.
(* This is a decent warmup, but TODO: example type application! *)

  Lemma sT_New_Syn Γ l (K : sf_kind Σ) T :
    oLater (oTMemK l K) :: Γ s⊨ oLater V⟦T⟧ ∷[ 0 ] K -∗
    Γ s⊨ vobj [ (l, dtysyn T) ] : oMu (oTMemK l K).
  Proof.
    rewrite -sT_Obj_I -sD_Sing'.
    apply sD_TypK_Abs_Syn.
  Qed.

  #[local] Notation IntoPersistent' P := (IntoPersistent false P P).
  #[global] Instance sstpiK_persistent i Γ T1 T2 K : IntoPersistent' (sstpiK i Γ T1 T2 K) := _.
  Lemma sT_New_Singl_Syn n Γ l (K : s_kind Σ n) T :
    oLater (oTMemK l (s_to_sf (ho_sing K (oLater V⟦T⟧)))) :: Γ s⊨ oLater V⟦T⟧ ∷[ 0 ] s_to_sf K -∗
    Γ s⊨ vobj [ (l, dtysyn T) ] : oMu (oTMemK l (s_to_sf K)).
  Proof using HswapProp.
    iIntros "#HT".
    iApply (sT_Sub (T1 := oMu _)).
    { rewrite sK_HoIntv. iApply (sT_New_Syn with "HT"). }
    iApply (sStp_Singl_Widen with "HT").
  Qed.

  (* Replacing [l] by [A], this rule looks like:

     Γ, z : ▷ { A :: S_K(▷ V⟦ T ⟧ᶻ) } s⊨ ▷ V⟦ T ⟧ᶻ ∷ Kᶻ
     ----------------------------------------------- (μ-<:-μ)
     Γ s⊨ { A := T }.A <: ▷ V⟦ T ⟧ [ z := { A := T } ] ∷ K [ z := { A := T } ]
  *)
  Lemma sKEq_New_Sel_Syn {n Γ l T} {K : s_kind Σ n} :
    let vPack := vobj [ (l, dtysyn T) ] in
    oLater (oTMemK l (s_to_sf (ho_sing K (oLater V⟦T⟧)))) :: Γ s⊨ oLater V⟦T⟧ ∷[ 0 ] s_to_sf K -∗
    Γ s⊨ oSel (pv vPack) l =[0] oLater V⟦T⟧ .sTp[ vPack /] ∷ s_to_sf K.|[ vPack /].
  Proof using HswapProp.
    iIntros (vPack) "#HK".
    iPoseProof (sK_HoSing with "HK") as "HK1".
    iDestruct (sT_New_Syn with "HK1") as "Hpn". fold vPack.
    iEval (rewrite sP_Val) in "Hpn".
    (* iDestruct (sT_New_Singl_Syn with "HK") as "Hpn'"; iEval (rewrite sP_Val) in "Hpn'". *)
    (* iDestruct (sKEq_New_Sel_Widen with "HK Hpn'") as "?". *)
    iApply (sKEq_New_Sel_Widen with "HK Hpn").
  Qed.
End lemmas.

Section examples.
  Context `{Hdlang : !dlangG Σ} `{HswapProp : SwapPropI Σ}.

  (* fmap! *)

End examples.
