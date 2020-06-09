(* (* Must be loaded first, so that other modules can reset some flags. *)
Require Import Equations.Equations. *)
From Coq Require FunctionalExtensionality.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
From D Require Import iris_prelude.
From D Require Export succ_notation.
From D Require Import saved_interp_dep asubst_intf asubst_base dlang lty.
From D Require Import swap_later_impl.
From D.Dot Require dot_lty unary_lr path_repl_lr.
From D.Dot Require defs_lr binding_lr dsub_lr sub_lr examples_lr.
From D.Dot Require hoas ex_utils.

From D.Dot Require Import sem_kind.

Set Suggest Proof Using.
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (Σ : gFunctors).


Module Type HoSemJudgments
  (Import VS : VlSortsSig)
  (Import LWP : LiftWp VS)
  (Import L : Lty VS LWP)
  (Import HST : HoSemTypes VS LWP L).

(** Kinded, Indexed SubTyPing *)
Definition sstpiK `{dlangG Σ} {n} i Γ T1 T2 (K : sf_kind Σ n) : iProp Σ :=
  □∀ ρ, sG⟦Γ⟧*ρ → ▷^i K ρ (envApply T1 ρ) (envApply T2 ρ).
Instance: Params (@sstpiK) 5 := {}.
Notation "Γ s⊨ T1 <:[ i  ] T2 ∷ K" := (sstpiK i Γ T1 T2 K)
  (at level 74, i, T1, T2, K at next level).

Notation "Γ s⊨ T1 =[ i  ] T2 ∷ K" :=
  (Γ s⊨ T1 <:[ i  ] T2 ∷ K ∧ Γ s⊨ T2 <:[ i  ] T1 ∷ K)%I
  (at level 74, i, T1, T2, K at next level).

Notation "Γ s⊨ T ∷[ i  ] K" := (Γ s⊨ T <:[ i ] T ∷ K)
  (at level 74, T, K at next level).

(* Semantic SubKinding *)
Definition sSkd `{dlangG Σ} {n} i Γ (K1 K2 : sf_kind Σ n) : iProp Σ :=
  □∀ ρ, sG⟦Γ⟧*ρ → ∀ (T1 T2 : hoLtyO Σ n), ▷^i (K1 ρ T1 T2 → K2 ρ T1 T2).
Instance: Params (@sSkd) 5 := {}.
Notation "Γ s⊨ K1 <∷[ i  ] K2" := (sSkd i Γ K1 K2)
  (at level 74, K1, K2 at next level).

Instance sstpiK_persistent `{dlangG Σ} {n} i Γ T1 T2 (K : sf_kind Σ n) :
  Persistent (Γ s⊨ T1 <:[ i  ] T2 ∷ K) := _.
Instance sSkd_persistent `{dlangG Σ} {n} i Γ (K1 K2 : sf_kind Σ n) :
  Persistent (Γ s⊨ K1 <∷[ i  ] K2) := _.

Section gen_lemmas.
  Context `{Hdlang : dlangG Σ} `{HswapProp: SwapPropI Σ}.

  Local Notation IntoPersistent' P := (IntoPersistent false P P).

  Global Instance sstpiK_into_persistent : IntoPersistent' (sstpiK (n := n) i Γ T1 T2 K) | 0 := _.
  Global Instance sSkd_into_persistent : IntoPersistent' (sSkd (n := n) i Γ K1 K2) | 0 := _.

  Global Instance sstpiK_proper n i :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡)) (sstpiK (Σ := Σ) (n := n) i).
  Proof.
    rewrite /sstpiK=> Γ1 Γ2 HΓ T1 T2 HT U1 U2 HU K1 K2 HK.
    properness; rewrite (HΓ, HK); first done.
    (* Time by rewrite HT HU. *)
    (* Time by apply sf_kind_sub_proper => //; f_equiv. *)
    by apply sf_kind_proper; f_equiv.
  Qed.

  Global Instance sSkd_proper n i :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (sSkd (Σ := Σ) (n := n) i).
  Proof.
    rewrite /sSkd => Γ1 Γ2 HΓ K1 K2 HK1 K3 K4 HK2.
    by properness; rewrite (HΓ, HK1, HK2).
  Qed.

  Lemma shift_sstpiK S Γ {n i} (T1 T2 : olty Σ n) K :
    Γ s⊨ T1 <:[ i ] T2 ∷ K -∗
    S :: Γ s⊨ oShift T1 <:[ i ] oShift T2 ∷ kShift K.
  Proof.
    iIntros "#HK !> %ρ /= #[Hg _]".
    by iApply (sf_kind_proper with "(HK Hg)").
  Qed.

  Lemma shift_sKEq S Γ {n i} (T1 T2 : olty Σ n) K :
    Γ s⊨ T1 =[ i ] T2 ∷ K -∗
    S :: Γ s⊨ oShift T1 =[ i ] oShift T2 ∷ kShift K.
  Proof. by rewrite -!shift_sstpiK. Qed.

  Lemma shift_stpkD S Γ {n i} (T : olty Σ n) K :
    Γ s⊨ T ∷[ i ] K -∗
    S :: Γ s⊨ oShift T ∷[ i ] kShift K.
  Proof. apply shift_sstpiK. Qed.

  Lemma shift_sSkd S Γ {n i} (K1 K2 : sf_kind Σ n) :
    Γ s⊨ K1 <∷[ i ] K2 -∗
    S :: Γ s⊨ kShift K1 <∷[ i ] kShift K2.
  Proof.
    iIntros "#HK !> * /= #[Hg _] *".
    iApply ("HK" with "Hg").
  Qed.

  Lemma narrow_sstpiK {n} Γ S1 S2 T U (K : sf_kind Σ n) i :
    S2 :: Γ s⊨ S2 <:[ 0 ] S1 ∷ sf_star -∗
    S1 :: Γ s⊨ T <:[ i ] U ∷ K -∗
    S2 :: Γ s⊨ T <:[ i ] U ∷ K.
  Proof.
    iIntros "#HsubS #HJ !> * /= #[Hg HS]".
    iApply ("HJ" $! ρ with "[$Hg]").
    iApply ("HsubS" $! ρ with "[$Hg $HS] HS").
  Qed.

  Lemma narrow_stpkD {n} Γ S1 S2 T (K : sf_kind Σ n) i :
    S2 :: Γ s⊨ S2 <:[ 0 ] S1 ∷ sf_star -∗
    S1 :: Γ s⊨ T ∷[ i ] K -∗
    S2 :: Γ s⊨ T ∷[ i ] K.
  Proof. apply narrow_sstpiK. Qed.

  Lemma narrow_sKEq {n} Γ S1 S2 T U (K : sf_kind Σ n) i :
    S2 :: Γ s⊨ S2 <:[ 0 ] S1 ∷ sf_star -∗
    S1 :: Γ s⊨ T =[ i ] U ∷ K -∗
    S2 :: Γ s⊨ T =[ i ] U ∷ K.
  Proof.
    by iIntros "#HsubS #[HJ1 HJ2]"; iSplit; iApply (narrow_sstpiK with "HsubS").
  Qed.

  Lemma narrow_sSkd Γ S1 S2 {n i} (K1 K2 : sf_kind Σ n) :
    S2 :: Γ s⊨ S2 <:[ 0 ] S1 ∷ sf_star -∗
    S1 :: Γ s⊨ K1 <∷[ i ] K2 -∗
    S2 :: Γ s⊨ K1 <∷[ i ] K2.
  Proof.
    iIntros "#HsubS #HJ !> * /= #[Hg HS] *".
    iApply ("HJ" $! ρ with "[$Hg]").
    iApply ("HsubS" $! ρ with "[$Hg $HS] HS").
  Qed.

  Lemma sKEq_Symm Γ {n} (K : sf_kind Σ n) T1 T2 i :
    Γ s⊨ T1 =[ i ] T2 ∷ K -∗
    Γ s⊨ T2 =[ i ] T1 ∷ K.
  Proof. iIntros "[$ $]". Qed.

  Lemma sf_star_eq ρ T1 T2 :
    sf_star ρ T1 T2 ⊣⊢ □ (oClose T1 ⊆@{Σ} oClose T2).
  Proof.
    iSplit; first by iIntros "(_ & $ & _)".
    iIntros "#$ !>"; iSplit;
      iIntros (v); [iIntros "[]" | iIntros "_ //"].
  Qed.

  Lemma ksubtyping_equiv i Γ T1 T2 :
    Γ s⊨ T1 <:[ i ] T2 ∷ sf_star ⊣⊢
    □(∀ ρ, sG⟦ Γ ⟧* ρ → ▷^i (oClose T1 ρ ⊆ oClose T2 ρ)).
  Proof.
    iSplit.
    - iIntros "#Hsub !> %ρ Hg".
      iDestruct (sf_star_eq with "(Hsub Hg)") as "{Hsub} Hsub".
      by rewrite -mlaterN_pers; iApply "Hsub".
    - iIntros "#Hsub !> %ρ #Hg"; rewrite sf_star_eq -mlaterN_pers /=.
      iModIntro; iApply ("Hsub" with "Hg").
  Qed.

  Lemma ksubtyping_spec ρ i Γ T1 T2 :
    Γ s⊨ T1 <:[ i ] T2 ∷ sf_star -∗
    sG⟦ Γ ⟧* ρ -∗
    ▷^i (oClose T1 ρ ⊆ oClose T2 ρ).
  Proof.
    rewrite ksubtyping_equiv; iIntros "Hsub Hg"; iApply ("Hsub" with "Hg").
  Qed.

  Lemma ksubtyping_intro i Γ (T1 T2 : oltyO Σ 0) :
    (□∀ ρ, sG⟦ Γ ⟧* ρ →
    ∀ v, ▷^i (oClose T1 ρ v → oClose T2 ρ v)) -∗
    Γ s⊨ T1 <:[ i ] T2 ∷ sf_star.
  Proof.
    apply equiv_entails. rewrite ksubtyping_equiv; properness; first done.
    by rewrite -laterN_forall.
  Qed.

  Lemma ksubtyping_intro_swap i Γ (T1 T2 : oltyO Σ 0) :
    (□∀ ρ, sG⟦ Γ ⟧* ρ →
    ∀ v, ▷^i oClose T1 ρ v → ▷^i oClose T2 ρ v) -∗
    Γ s⊨ T1 <:[ i ] T2 ∷ sf_star.
  Proof using HswapProp.
    rewrite -ksubtyping_intro; iIntros "#Hsub !> * #Hg *".
    iApply (impl_laterN with "(Hsub Hg)").
  Qed.

  Lemma kinding_intro Γ i (L T U : oltyO Σ 0) :
    (□∀ ρ, sG⟦ Γ ⟧* ρ →
    ▷^i □(oClose L ρ ⊆ oClose T ρ ⊆ oClose U ρ)) -∗
    Γ s⊨ T ∷[ i ] sf_kintv L U.
  Proof.
    iIntros "#Hsub !>" (ρ); rewrite /= sr_kintv_refl /=. iApply "Hsub".
  Qed.

  (** * Prefixes: K for Kinding, KStp for kinded subtyping, Skd for subkinding. *)

  Definition sf_sngl (T : oltyO Σ 0) : sf_kind Σ 0 := sf_kintv T T.

  Lemma sK_Sing Γ (T : oltyO Σ 0) i :
    ⊢ Γ s⊨ T ∷[ i ] sf_sngl T.
  Proof.
    rewrite -kinding_intro; iIntros "!> %ρ _". by rewrite -subtype_refl.
  Qed.

  Lemma sKStp_Intv Γ (T1 T2 L U : oltyO Σ 0) i :
    Γ s⊨ T1 <:[i] T2 ∷ sf_kintv L U -∗
    Γ s⊨ T1 <:[i] T2 ∷ sf_kintv T1 T2.
  Proof.
    iIntros "#Hs !> * Hg"; iDestruct ("Hs" with "Hg") as "{Hs} (_ & #H & _)".
    rewrite /= /sr_kintv; iNext i; iModIntro. iDestruct "H" as "#$ {H}".
    by rewrite -!subtype_refl.
  Qed.

  (** Kind subsumption (for kinded subtyping). *)
  Lemma sKStp_Sub Γ {n} (T1 T2 : oltyO Σ n) (K1 K2 : sf_kind Σ n) i :
    Γ s⊨ T1 <:[ i ] T2 ∷ K1 -∗
    Γ s⊨ K1 <∷[ i ] K2 -∗
    Γ s⊨ T1 <:[ i ] T2 ∷ K2.
  Proof.
    iIntros "#H1 #Hsub !> %ρ #Hg". iApply ("Hsub" with "Hg (H1 Hg)").
  Qed.

  (** Kind subsumption (for kinding). *)
  Lemma sK_Sub Γ {n} (T : oltyO Σ n) (K1 K2 : sf_kind Σ n) i :
    Γ s⊨ T ∷[ i ] K1 -∗
    Γ s⊨ K1 <∷[ i ] K2 -∗
    Γ s⊨ T ∷[ i ] K2.
  Proof. apply sKStp_Sub. Qed.

  Lemma sKStp_Lam Γ {n} (K : sf_kind Σ n) S T1 T2 i :
    oLaterN i (oShift S) :: Γ s⊨ T1 <:[i] T2 ∷ K -∗
    Γ s⊨ oLam T1 <:[i] oLam T2 ∷ sf_kpi S K.
  Proof using HswapProp.
    iIntros "#HTK !> * #Hg * /=" (arg).
    rewrite -mlaterN_pers -impl_laterN.
    iIntros "!> Hs".
    iSpecialize ("HTK" $! (arg .: ρ) with "[$Hg $Hs]").
    by iApply (sf_kind_proper with "HTK").
  Qed.

  Lemma sK_Lam Γ {n} (K : sf_kind Σ n) S T i :
    oLaterN i (oShift S) :: Γ s⊨ T ∷[i] K -∗
    Γ s⊨ oLam T ∷[i] sf_kpi S K.
  Proof using HswapProp. apply sKStp_Lam. Qed.

  (** * Subkinding *)
  Lemma sSkd_Intv (L1 L2 U1 U2 : oltyO Σ 0) Γ i :
    Γ s⊨ L2 <:[ i ] L1 ∷ sf_star -∗
    Γ s⊨ U1 <:[ i ] U2 ∷ sf_star -∗
    Γ s⊨ sf_kintv L1 U1 <∷[ i ] sf_kintv L2 U2.
  Proof.
    iIntros "#HsubL #HsubU !> * #Hg /=" (T1 T2).
    iPoseProof (ksubtyping_spec with "HsubL Hg") as "{HsubL} HsubL".
    iPoseProof (ksubtyping_spec with "HsubU Hg") as "{HsubU Hg} HsubU".
    iNext i; iIntros "#(HsubL1 & $ & HsubU1) !>"; iSplit.
    iApply (subtype_trans with "HsubL HsubL1").
    iApply (subtype_trans with "HsubU1 HsubU").
  Qed.

  Lemma sSkd_Pi {n} (S1 S2 : oltyO Σ 0) (K1 K2 : sf_kind Σ n) Γ i :
    Γ s⊨ S2 <:[ i ] S1 ∷ sf_star -∗
    oLaterN i (oShift S2) :: Γ s⊨ K1 <∷[ i ] K2 -∗
    Γ s⊨ sf_kpi S1 K1 <∷[ i ] sf_kpi S2 K2.
  Proof using HswapProp.
    iIntros "#HsubS #HsubK !> %ρ #Hg /=".
    iPoseProof (ksubtyping_spec with "HsubS Hg") as "{HsubS} HsubS".
    iAssert (□∀ arg : vl, let ρ' := arg .: ρ in
            ▷^i (oClose S2 ρ arg → ∀ T1 T2 : hoLtyO Σ n,
            K1 ρ' T1 T2 → K2 ρ' T1 T2))%I as
            "{HsubK} #HsubK". {
      iIntros "%arg !>"; rewrite -mlaterN_impl.
      iIntros "#HS2 %T1 %T2"; rewrite -mlaterN_impl; iIntros "HK1".
      iApply ("HsubK" $! (arg .: ρ) with "[$Hg $HS2] HK1").
    }
    iIntros (T1 T2); iNext i; iIntros "#HTK1 !> * #HS".
    iSpecialize ("HsubK" $! arg with "HS").
    iApply ("HsubK" with "(HTK1 (HsubS HS))").
  Qed.

  (** Reflexivity and transitivity of subkinding seem admissible, but let's
  prove them anyway, to show they hold regardless of extensions. *)
  Lemma sSkd_Refl {n} Γ i (K : sf_kind Σ n) :
    ⊢ Γ s⊨ K <∷[ i ] K.
  Proof. iIntros "!> * Hg * !> $". Qed.

  Lemma sSkd_Trans {n} Γ i (K1 K2 K3 : sf_kind Σ n) :
    Γ s⊨ K1 <∷[ i ] K2 -∗
    Γ s⊨ K2 <∷[ i ] K3 -∗
    Γ s⊨ K1 <∷[ i ] K3.
  Proof.
    iIntros "#Hs1 #Hs2 !> * #Hg *".
    iSpecialize ("Hs1" with "Hg"); iSpecialize ("Hs2" with "Hg"); iNext i.
    iIntros "{Hg} HK1". iApply ("Hs2" with "(Hs1 HK1)").
  Qed.

  (** * Kinded subtyping. *)

  Lemma sKStp_Refl Γ {n} T (K : sf_kind Σ n) i :
    Γ s⊨ T ∷[ i ] K -∗
    Γ s⊨ T <:[ i ] T ∷ K.
  Proof. done. Qed.

  Lemma sKEq_Refl {n} Γ T1 T2 (K : sf_kind Σ n) i :
    T1 ≡ T2 →
    Γ s⊨ T1 ∷[i] K -∗
    Γ s⊨ T1 =[i] T2 ∷ K.
  Proof. iIntros (Heq) "#H"; by iSplit; iApply (sstpiK_proper with "H"). Qed.

  Lemma sTEq_Eta {n} (T : oltyO Σ n.+1) :
    T ≡ oLam (oTAppV (oShift T) (ids 0)).
  Proof. move => + ρ v. apply: vec_S_inv => w args. autosubst. Qed.

  Lemma sKEq_Eta {n} Γ S T (K : sf_kind Σ n) i :
    Γ s⊨ T ∷[i] sf_kpi S K -∗
    Γ s⊨ T =[i] oLam (oTAppV (oShift T) (ids 0)) ∷ sf_kpi S K.
  Proof. iApply sKEq_Refl. apply sTEq_Eta. Qed.

  Lemma sKStp_Trans Γ {n} T1 T2 T3 (K : sf_kind Σ n) i :
    Γ s⊨ T1 <:[ i ] T2 ∷ K -∗
    Γ s⊨ T2 <:[ i ] T3 ∷ K -∗
    Γ s⊨ T1 <:[ i ] T3 ∷ K.
  Proof.
    iIntros "#Hs1 #Hs2 !> * #Hg".
    iApply (sf_kind_sub_trans with "(Hs1 Hg) (Hs2 Hg)").
  Qed.

  (* Notation "" := sf_star. *)
  (* Notation "L  U" := (sf_kintv L U) (at level 70). *)

  Lemma sKStp_Top Γ (T : oltyO Σ 0) i :
    ⊢ Γ s⊨ T <:[ i ] ⊤ ∷ sf_star.
  Proof. rewrite -ksubtyping_intro. iIntros "!> * _ * !> _ //". Qed.
  Lemma sKStp_Bot Γ (T : oltyO Σ 0) i :
    ⊢ Γ s⊨ ⊥ <:[ i ] T ∷ sf_star.
  Proof. rewrite -ksubtyping_intro; iIntros "!> * _ * !> []". Qed.

  (* XXX <:-..-U *)
  Lemma sKStp_IntvU {Γ T1 T2 L U i} :
    Γ s⊨ T1 <:[i] T2 ∷ sf_kintv L U -∗
    Γ s⊨ T2 <:[i] U ∷ sf_star.
  Proof.
    rewrite -ksubtyping_intro; iIntros "#HK !> * Hg *".
    iDestruct ("HK" with "Hg") as "[_ [_ Hsub]]".
    iNext i; iApply "Hsub".
  Qed.

  (* <:-..-U *)
  Lemma sKStp_IntvU' {Γ T L U i} :
    Γ s⊨ T ∷[i] sf_kintv L U -∗
    Γ s⊨ T <:[i] U ∷ sf_star.
  Proof. apply sKStp_IntvU. Qed.

  (* <:-..-L *)
  Lemma sKStp_IntvL {Γ T1 T2 L U i} :
    Γ s⊨ T1 <:[i] T2 ∷ sf_kintv L U -∗
    Γ s⊨ L <:[i] T1 ∷ sf_star.
  Proof.
    rewrite -ksubtyping_intro; iIntros "#HK !> * Hg *".
    iDestruct ("HK" with "Hg") as "[Hsub _]".
    iNext i; iApply "Hsub".
  Qed.

  Lemma sKStp_IntvL' {Γ T L U i} :
    Γ s⊨ T ∷[i] sf_kintv L U -∗
    Γ s⊨ L <:[i] T ∷ sf_star.
  Proof. apply sKStp_IntvL. Qed.

  (* Must be primitive *)
  Lemma sKStp_Intv_Split Γ T1 T2 L U i :
    Γ s⊨ L  <:[i] T1 ∷ sf_star -∗
    Γ s⊨ T1 <:[i] T2 ∷ sf_star -∗
    Γ s⊨ T2 <:[i] U  ∷ sf_star -∗
    Γ s⊨ T1 <:[i] T2 ∷ sf_kintv L U.
  Proof.
    iIntros "#HL #HT #HU !>" (ρ) "#HG"; rewrite !(ksubtyping_spec ρ).
    rewrite /= /sr_kintv -mlaterN_pers; iModIntro.
    by repeat iSplit; [iApply "HL"|iApply "HT"|iApply "HU"].
  Qed.

End gen_lemmas.

End HoSemJudgments.

Module HkDot.
Import dot_lty unary_lr dsub_lr sub_lr path_repl_lr hoas ex_utils.
Export HkDotSemTypes.
Include HoSemJudgments VlSorts dlang_inst dot_lty HkDotSemTypes.
Implicit Types
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : var → vl) (l : label).

Notation "Γ s⊨X T1 <:[ i  ] T2 " := (sstpd i Γ T1 T2) (at level 74, T1, T2 at next level).

Section dot_types.
  Context `{!dlangG Σ} `{HswapProp: SwapPropI Σ}.

  (** Such substitution lemmas hold for all judgments. Note the mu type!
  XXX don't restrict to values. *)
  Lemma sptp_subst_oMu {Γ T U p v i} :
    Γ s⊨p pv v : oMu T, i -∗
    oLaterN i T :: Γ s⊨p p : U, i -∗
    Γ s⊨p p.|[v/] : U.|[v/], i.
  Proof.
    iIntros "#Hrepl #H !>" (ρ) "#Hg /=".
    iSpecialize ("Hrepl" with "Hg"); rewrite path_wp_pv_eq.
    rewrite hsubst_comp -subst_swap_base.
    iSpecialize ("H" $! (v.[ρ] .: ρ) with "[$Hg $Hrepl]").
    iApply (path_wp_wand with "H"); iIntros "!>" (w) "Hw".
    by rewrite /= hoEnvD_subst_one.
  Qed.

  (* Add a lemma like [sptp_subst_oMu], used below. *)
  (* We need a semantic substitution lemma?!? More importantly... one with mu types!?!? Oh dear. *)
  Lemma sstpiK_subst_oMu {n} (K : sf_kind Σ n){Γ V T1 T2 v i}  :
    Γ s⊨p pv v : oMu V, i -∗
    oLaterN i V :: Γ s⊨ T1 <:[ i ] T2 ∷ K -∗
    Γ s⊨ T1.|[v/] <:[ i ] T2.|[v/] ∷ K.|[v/].
  Proof.
    iIntros "#Hrepl #H !>" (ρ) "#Hg /=".
    iSpecialize ("Hrepl" with "Hg"); rewrite path_wp_pv_eq -subst_swap_base.
    iSpecialize ("H" $! (v.[ρ] .: ρ) with "[$Hg $Hrepl]").
    iApply (sf_kind_proper with "H") => args w /=;
      by rewrite hoEnvD_subst_one.
  Qed.

  Lemma sKStp_App Γ {n} (K : sf_kind Σ n) S T1 T2 i p :
    Γ s⊨ T1 <:[i] T2 ∷ sf_kpi S K -∗
    Γ s⊨p p : S, i -∗
    Γ s⊨ oTApp T1 p <:[i] oTApp T2 p ∷ kpSubstOne p K.
  Proof.
    iIntros "#HTK #Hp !> * #Hg".
    iApply (strong_path_wp_wand with "(Hp Hg)").
    iIntros (v Hal%alias_paths_pv_eq_1) "{Hp} #Hv".
    iApply (sf_kind_proper with "(HTK Hg Hv)") => args w /=;
      by rewrite (alias_paths_elim_eq _ Hal) path_wp_pv_eq.
  Qed.

  Lemma sK_App Γ {n} (K : sf_kind Σ n) S T i p :
    Γ s⊨ T ∷[i] sf_kpi S K -∗
    Γ s⊨p p : S, i -∗
    Γ s⊨ oTApp T p ∷[i] kpSubstOne p K.
  Proof. apply sKStp_App. Qed.

  (* Maybe not interesting *)
  Lemma sKStp_AppV Γ {n} (K : sf_kind Σ n) {S T1 T2 i v} :
    Γ s⊨ T1 <:[i] T2 ∷ sf_kpi S K -∗
    Γ s⊨p pv v : S, i -∗
    Γ s⊨ oTAppV T1 v <:[i] oTAppV T2 v ∷ K.|[v/].
  Proof.
    rewrite -!oTApp_pv. iIntros "#HTK #Hv !> * #Hg"; rewrite kpSubstOne_eq.
    iApply (sKStp_App with "HTK Hv Hg").
  Qed.

  Lemma sK_AppV Γ {n} (K : sf_kind Σ n) {S T i v} :
    Γ s⊨ T ∷[i] sf_kpi S K -∗
    Γ s⊨p pv v : S, i -∗
    Γ s⊨ oTAppV T v ∷[i] K.|[v/].
  Proof. apply sKStp_AppV. Qed.


  (* XXX Those two semantic types are definitionally equal; show that opSubst
  agrees with syntactic path substitution for gDOT.
  The closest thing we can state is [sem_psubst_one_eq]. *)
  Lemma sKEq_Beta {n} Γ S T (K : sf_kind Σ n) i p :
    Γ s⊨p p : S, i -∗
    oLaterN i (oShift S) :: Γ s⊨ T ∷[i] K -∗
    Γ s⊨ oTApp (oLam T) p =[i] T .sTp[ p /] ∷ kpSubstOne p K.
  Proof using HswapProp.
    iIntros "#Hp #HK"; iApply sKEq_Refl. apply sTEq_Beta.
    rewrite sK_Lam. iApply (sK_App with "HK Hp").
  Qed.

  Lemma sKEq_BetaV {n} Γ S T (K : sf_kind Σ n) i v :
    Γ s⊨p pv v : S, i -∗
    oLaterN i (oShift S) :: Γ s⊨ T ∷[i] K -∗
    Γ s⊨ oTAppV (oLam T) v =[i] T.|[v/] ∷ K.|[v/].
  Proof using HswapProp.
    (* Reuses other lemma but slow. *)
    (* rewrite -oTApp_pv -opSubst_pv_eq kpSubstOne_eq.
    apply sKEq_Beta. *)
    iIntros "#Hv #HK"; iApply sKEq_Refl. apply sTEq_BetaV.
    rewrite sK_Lam; iApply (sK_AppV with "HK Hv").
  Qed.


  Lemma sstpiK_star_to_sstp Γ i T1 T2 :
    Γ s⊨ T1 <:[ i ] T2 ∷ sf_star ⊢ Γ s⊨ T1 , i <: T2 , i.
  Proof.
    iIntros "#Hsub !> %ρ %v #Hg".
    iDestruct (ksubtyping_spec with "Hsub Hg") as "{Hsub Hg} Hsub".
    rewrite -laterN_impl. iNext i. iApply ("Hsub" $! v).
  Qed.

  Lemma sstpiK_star_eq_sstp Γ i T1 T2 :
    Γ s⊨ T1 <:[ i ] T2 ∷ sf_star ⊣⊢ Γ s⊨ T1 , i <: T2 , i.
  Proof using HswapProp.
    iSplit; first iApply sstpiK_star_to_sstp.
    rewrite -ksubtyping_intro_swap /=. iIntros "#Hsub !> * Hg *".
    iApply ("Hsub" with "Hg").
  Qed.

  Lemma sstpiK_star_eq_sstpd Γ i T1 T2 :
    Γ s⊨ T1 <:[ i ] T2 ∷ sf_star ⊣⊢ Γ s⊨X T1 <:[ i ] T2.
  Proof. apply ksubtyping_equiv. Qed.


  Lemma sKStp_TMem {n} Γ l (K1 K2 : sf_kind Σ n) i :
    Γ s⊨ K1 <∷[ i ] K2 -∗
    Γ s⊨ cTMemK l K1 <:[ i ] cTMemK l K2 ∷ sf_star.
  Proof.
    rewrite -ksubtyping_intro; iIntros "#HK !> * Hg *".
    iSpecialize ("HK" with "Hg"); iNext i.
    iDestruct 1 as (d Hld) "Hφ"; iExists d; iFrame (Hld).
    iDestruct "Hφ" as (φ) "[Hlφ #HK1]"; iExists φ; iFrame "Hlφ".
    iApply ("HK" with "HK1").
  Qed.

  Lemma sKStp_TMem_AnyKind {n} Γ l (K : sf_kind Σ n) i :
    ⊢ Γ s⊨ cTMemK l K <:[ i ] cTMemAnyKind l ∷ sf_star.
  Proof.
    rewrite -ksubtyping_intro; iIntros "!> * #Hg * !>".
    iDestruct 1 as (d Hl φ) "[Hl _]".
    iExists d; iFrame (Hl); iExists n, φ; iFrame "Hl".
  Qed.

  (** * Kinding *)
  Lemma sK_Star Γ (T : oltyO Σ 0) i :
    ⊢ Γ s⊨ T ∷[ i ] sf_star.
  Proof.
    iApply sK_Sub. iApply sK_Sing.
    iApply sSkd_Intv; rewrite sstpiK_star_eq_sstpd.
    by iApply sBot_Stp.
    by iApply sStp_Top.
  Qed.

  (** Generalization of [sD_Typ_Abs]. *)
  Lemma sD_TypK_Abs {Γ n} T (K : sf_kind Σ n) s σ l:
    Γ s⊨ oLater T ∷[ 0 ] K -∗
    s ↝[ σ ] T -∗
    Γ s⊨ { l := dtysem σ s } : cTMemK l K.
  Proof.
    rewrite sdtp_eq'; iIntros "#HTK"; iDestruct 1 as (φ Hγφ) "#Hγ".
    iIntros "!>" (ρ Hpid) "Hg"; iExists (hoEnvD_inst (σ.|[ρ]) φ); iSplit.
    by iApply (dm_to_type_intro with "Hγ").
    iApply (sf_kind_proper' with "(HTK Hg)") => args v /=.
    by rewrite -(Hγφ args ρ v) make_intuitionistically.
  Qed.

  Lemma sK_Sel {Γ n} l (K : sf_kind Σ n) p i :
    Γ s⊨p p : cTMemK l K, i -∗
    Γ s⊨ oSelN n p l ∷[i] K.
  Proof.
    iIntros "#Hp !> * Hg"; iSpecialize ("Hp" with "Hg"); iNext i.
    rewrite path_wp_eq.
    iDestruct "Hp" as (v Hal%alias_paths_pv_eq_1 d1 Hl1 ψ1) "[#Hl1 HK]".
    iApply (sfkind_respects with "[] HK"); iIntros (args w) "!>".
    rewrite /= (alias_paths_elim_eq _ Hal) path_wp_pv_eq.
    iSplit; first by iIntros "H"; iExists d1, ψ1; iFrame (Hl1) "Hl1".
    iDestruct 1 as (d2 ψ2 Hl2) "[Hl2 Hw]"; objLookupDet.
    iDestruct (dm_to_type_agree args w with "Hl1 Hl2") as "Hag {Hl1}".
    iNext. by iRewrite "Hag".
  Qed.

  Lemma sSngl_pq_KStp {Γ i p q n T1 T2} {K : sf_kind Σ n} :
    T1 ~sTpI[ p := q ]* T2 -∗
    Γ s⊨p p : oSing q, i -∗
    Γ s⊨ T1 ∷[i] K -∗
    Γ s⊨ T1 <:[i] T2 ∷ K.
  Proof.
    iIntros "#Hrepl #Hal #HK !> * #Hg".
    iSpecialize ("Hal" with "Hg"); iSpecialize ("HK" with "Hg"); iNext i.
    iDestruct "Hal" as %Hal%alias_paths_simpl.
    iApply (sf_kind_sub_internal_proper with "[] [] HK").
    iApply hoLty_equiv_refl.
    iIntros "!> %args %v"; rewrite -internal_eq_iff.
    iApply ("Hrepl" $! args ρ v Hal).
  Qed.

  (* This is the easy part :-) *)
  Lemma sSngl_pq_KStp' {Γ i p q n T1 T2} {K1 K2 : sf_kind Σ n}
    (* XXX we should use an internal version of this premise, as done for [sSngl_pq_KStp]. *)
    (Hrepl : K1 ~sKd[ p := q ]* K2) :
    Γ s⊨p p : oSing q, i -∗
    Γ s⊨ T1 <:[i] T2 ∷ K1 -∗
    Γ s⊨ T1 <:[i] T2 ∷ K2.
  Proof.
    iIntros "#Hal #HK !> * #Hg".
    iSpecialize ("Hal" with "Hg"); iSpecialize ("HK" with "Hg"). iNext i.
    iDestruct "Hal" as %Hal%alias_paths_simpl.
    by iApply (Hrepl with "HK").
  Qed.

End dot_types.

(*
(** Nope, use a more syntactic definition, else proving [ho_intv_proper]
becomes hopeless. *)
Section s_kind_ofe.
  Context {Σ} {n : nat}.
  Notation tpred := (s_kind Σ n).
  (* Forces inserting coercions to -d>. *)

  Instance s_kind_equiv : Equiv tpred := λ A B, A ≡@{sf_kind _ _} B.
  Instance s_kind_dist : Dist tpred := λ n A B, A ≡{n}@{sf_kind _ _}≡ B.
  Lemma s_kind_ofe_mixin : OfeMixin tpred.
  Proof. by apply (iso_ofe_mixin s_kind_to_sf_kind). Qed.
  Canonical Structure s_kindO := OfeT tpred s_kind_ofe_mixin.

  Lemma s_kind_equiv_intro (K1 K2 : sf_kind Σ n) : K1 ≡@{sf_kind _ _} K2 → K1 ≡ K2.
  Proof. apply. Qed.
End s_kind_ofe.
Global Arguments s_kindO : clear implicits. *)

Import defs_lr binding_lr examples_lr.

Section derived.
  Context `{Hdlang : !dlangG Σ} `{HswapProp : SwapPropI Σ}.
  Opaque sSkd sstpiK sptp sstpi.

  Lemma sT_New_w_And n Γ l σ s (K : sf_kind Σ n) T :
    oLater (cAnd (cTMemK l K) cTop) :: Γ s⊨ oLater T ∷[ 0 ] K -∗
    s ↝[ σ ] T -∗
    Γ s⊨ vobj [ (l, dtysem σ s) ] : oMu (cAnd (cTMemK l K) cTop).
  Proof.
    iIntros "#HT #Hs".
    iApply sT_Obj_I; iApply sD_Cons; [done| |iApply sD_Nil].
    iApply (sD_TypK_Abs with "HT Hs").
  Qed.

  (* Replace (U ∧ ⊤) by U. *)
  (* Closer to what Sandro wrote on paper, but some adjustments can only be
  done in the model, right now. *)
  Lemma sT_New_No_And {n Γ l σ s T} {K : sf_kind Σ n} :
    oLater (cTMemK l K) :: Γ s⊨ oLater T ∷[ 0 ] K -∗
    s ↝[ σ ] T -∗
    Γ s⊨ vobj [ (l, dtysem σ s) ] : oMu (cTMemK l K).
  Proof.
    have ->: (clty_olty (cTMemK l K) ≡ cAnd (cTMemK l K) cTop).
    by intros ???; iSplit; [iIntros "$" | iIntros "[$ _]"].
    apply sT_New_w_And.
  Qed.

  Lemma sKStp_Intv_Equiv {Γ T1 T2 L U i} :
    Γ s⊨ T1 <:[i] T2 ∷ sf_kintv L U ⊣⊢
    Γ s⊨ L <:[i] T1 ∷ sf_star ∗
    Γ s⊨ T1 <:[i] T2 ∷ sf_star ∗
    Γ s⊨ T2 <:[i] U ∷ sf_star.
  Proof.
    iSplit.
    - rewrite -(sKStp_IntvL (T2 := T2) (L := L) (U := U)).
      rewrite -(sKStp_IntvU (T1 := T1) (L := L) (U := U)).
      iIntros "#HK"; iFrame "HK".
      iApply (sKStp_Sub with "HK").
      iApply sSkd_Intv; [iApply sKStp_Bot|iApply sKStp_Top].
    - iIntros "#(HL & HT & HU)". iApply (sKStp_Intv_Split with "HL HT HU").
  Qed.

  Import SKindSyn.

  Lemma sK_Eta_Apply {n} Γ (K : s_kind Σ n) S T1 T2 i :
    Γ s⊨ T1 <:[ i ] T2 ∷ sf_kpi S K -∗
    oLaterN i (oShift S) :: Γ s⊨
      oTAppV (oShift T1) (ids 0) <:[i] oTAppV (oShift T2) (ids 0) ∷ K.
  Proof.
    iIntros "HK".
    rewrite (shift_sstpiK (oLaterN i (oShift S))) kShift_sf_kpi_eq.
    (* Either *)
    iEval rewrite -(kShift_cancel' K).
    iApply (sKStp_AppV _ _ (S := oShift S) with "HK").
    (* Or *)
    (* rewrite (sKStp_AppV _ _ (S := oShift S) (v := ids 0)) .
    rewrite (kShift_cancel' K).
    iApply "HK". *)

    (* And then in both cases: *)
    rewrite -(sP_LaterN (i := 0)). by iApply sP_Var0.
  Qed.

  Lemma sK_HoIntv {n} Γ (K : s_kind Σ n) T1 T2 i :
    Γ s⊨ T1 <:[i] T2 ∷ K -∗
    Γ s⊨ T1 <:[i] T2 ∷ ho_intv K T1 T2.
  Proof using HswapProp.
    elim: K Γ T1 T2 => [S1 S2|{}n S K IHK] Γ T1 T2 /=; iIntros "HK".
    - by iApply sKStp_Intv.
    (* XXX Here we rewrite using untyped equality *)
    - by rewrite sK_Eta_Apply IHK sKStp_Lam -!sTEq_Eta.
  Qed.

  Lemma ho_sing_idemp {n} (K : s_kind Σ n) T :
    ho_sing (ho_sing K T) T ≡@{sf_kind _ _}
    ho_sing K T.
  Proof. elim: K T => [//|{}n S K +] T /=. by move->. Qed.

  Lemma sKStp_HoIntvU {n} (K : s_kind Σ n) {Γ T1 T2 L U i} :
    Γ s⊨ T1 <:[i] T2 ∷ ho_intv K L U -∗
    (* Γ s⊨ T2 <:[i] U ∷ K. *) (* False*)
    Γ s⊨ T2 <:[i] U ∷ ho_intv K L U.
  Proof using HswapProp.
    elim: K Γ T1 T2 L U => /= [S1 S2|{}n S K IHK] Γ T1 T2 L U.
    - rewrite (sKStp_Intv_Equiv (T1 := T2)) (sKStp_Intv_Equiv (T1 := T1)).
      rewrite -sK_Star (right_id emp%I bi_sep).
      iIntros "(#HL & #HT & $)".
      iApply (sKStp_Trans with "HL HT").
      (* XXX Here we rewrite using untyped equality *)
    - by rewrite sK_Eta_Apply IHK sKStp_Lam -!sTEq_Eta.
  Qed.

  Lemma sKStp_HoIntvL {n} (K : s_kind Σ n) {Γ T1 T2 L U i} :
    Γ s⊨ T1 <:[i] T2 ∷ ho_intv K L U -∗
    (* Γ s⊨ L <:[i] T1 ∷ K. *) (* False*)
    (* Γ s⊨ T2 <:[i] U ∷ K. *) (* False*)
    Γ s⊨ L <:[i] T1 ∷ ho_intv K L U.
  Proof using HswapProp.
    elim: K Γ T1 T2 L U => /= [S1 S2|{}n S K IHK] Γ T1 T2 L U.
    - rewrite (sKStp_Intv_Equiv (T1 := L)) (sKStp_Intv_Equiv (T1 := T1)).
      rewrite -sK_Star (left_id emp%I bi_sep).
      iIntros "($ & #HT & HU)".
      iApply (sKStp_Trans with "HT HU").
      (* XXX Here we rewrite using untyped equality *)
    - by rewrite sK_Eta_Apply IHK sKStp_Lam -!sTEq_Eta.
  Qed.

  Lemma sKEq_HoSing {n} (K : s_kind Σ n) Γ T U i :
    Γ s⊨ T ∷[i] ho_sing K U -∗
    Γ s⊨ T =[i] U ∷ ho_sing K U.
  Proof using HswapProp.
    iIntros "#HK"; iSplit.
    by iApply sKStp_HoIntvU.
    by iApply sKStp_HoIntvL.
  Qed.

  Lemma sK_HoSing {n} Γ (K : s_kind Σ n) T i :
    Γ s⊨ T ∷[i] K -∗ Γ s⊨ T ∷[i] ho_sing K T.
  Proof using HswapProp. apply sK_HoIntv. Qed.

  (* to_rename, and should this be primitive? *)
  Lemma sSkd_Intv_Sub Γ L U T1 T2 i :
    Γ s⊨ T1 <:[ i ] T2 ∷ sf_kintv L U -∗
    Γ s⊨ sf_kintv T1 T2 <∷[ i ] sf_kintv L U.
  Proof.
    iIntros "#HK".
    iApply sSkd_Intv.
    iApply (sKStp_IntvL with "HK").
    iApply (sKStp_IntvU with "HK").
  Qed.

  Lemma sSkd_HoIntv {n} Γ (K : s_kind Σ n) T1 T2 i :
    Γ s⊨ T1 <:[i] T2 ∷ K -∗
    Γ s⊨ ho_intv K T1 T2 <∷[i] K .
  Proof using HswapProp.
    elim: K Γ T1 T2 => [S1 S2|{}n S K IHK] Γ T1 T2 /=; first iApply sSkd_Intv_Sub.
    iIntros "HK".
    iApply sSkd_Pi; first by iApply sK_Star.
    iApply IHK; iApply (sK_Eta_Apply with "HK").
  Qed.

  Lemma sT_New_Singl n Γ l σ s (K : s_kind Σ n) (T : olty Σ n) :
    oLater (cTMemK l (ho_sing K (oLater T))) :: Γ s⊨ oLater T ∷[ 0 ] K -∗
    s ↝[ σ ] T -∗
    Γ s⊨ vobj [ (l, dtysem σ s) ] : oMu (cTMemK l K).
  Proof using HswapProp.
    iIntros "#HT #Hs".
    iApply (sT_Sub (T1 := oMu (cTMemK l (ho_sing K (oLater T))))).
    rewrite sK_HoIntv; iApply (sT_New_No_And with "HT Hs").
    iApply sMu_Stp_Mu. rewrite oLaterN_0.
    rewrite -sstpiK_star_eq_sstpd.
    iApply sKStp_TMem.
    iApply sSkd_HoIntv.
    iApply (narrow_sstpiK with "[] HT").
    iApply sstpiK_star_eq_sstpd.
    iApply sStp_Add_Later.
  Qed.

  (* Global Instance : Params (@bi_wand b) 1 := {}. *)

  (** Kind subsumption (for kinded subtyping). *)
  Lemma sKEq_Sub Γ {n} (T1 T2 : oltyO Σ n) (K1 K2 : sf_kind Σ n) i :
    Γ s⊨ T1 =[ i ] T2 ∷ K1 -∗
    Γ s⊨ K1 <∷[ i ] K2 -∗
    Γ s⊨ T1 =[ i ] T2 ∷ K2.
  Proof.
    iIntros "#(Hs1 & Hs2) #HKs"; iSplit; by iApply (sKStp_Sub with "[] HKs").
  Qed.
(* Inductive s_kind {Σ} : nat → Type :=
  | s_kintv : olty Σ 0 → olty Σ 0 → s_kind 0
  | s_kpi n : olty Σ 0 → s_kind n → s_kind n.+1. *)

  (* XXX: Substituting [vPack] in types doesn't work robustly, so we should use an
  object-level [let] instead, or just assumptions on the typing context. *)
  Lemma sKEq_New_Sel {n Γ l σ s T} {K : s_kind Σ n} :
    (* oLater (cTMemK l K) :: Γ s⊨ oLater T ∷[ 0 ] K -∗ *)
    (* oLater (cAnd (cTMemK l K) cTop) :: Γ s⊨ oLater T ∷[ 0 ] K -∗ *)
    let vPack := vobj [ (l, dtysem σ s) ] in
    oLater (cTMemK l (ho_sing K (oLater T))) :: Γ s⊨ oLater T ∷[ 0 ] K -∗
    s ↝[ σ ] T -∗
      Γ s⊨ oSelN n (pv vPack) l =[0] oLater T .sTp[ vPack /] ∷ K.|[ vPack /].
  Proof using HswapProp.
    iIntros (vPack) "#HK #Hs".
    iPoseProof (sK_HoSing with "HK") as "HK1".
    (* iPoseProof (sP_New_w_And with "HK1 Hs") as "{HK1} Hpn". *)
    iPoseProof (sT_New_No_And with "HK1 Hs") as "{HK1} Hpn"; fold vPack.
    rewrite sP_Val.

    iApply (sKEq_Sub _ _ _ (ho_intv _ _ _)); last iApply sSkd_HoIntv.
    - iApply sKEq_HoSing. iApply sK_Sel.
      (* rewrite opSubst_pv_eq.
      rewrite -(ho_intv_subst K) -s_kind_to_sf_kind_subst -cTMemK_subst.
      rewrite -opSubst_pv_eq.
      iApply sP_Mu_E. *)
      rewrite sP_Mu_E.
      rewrite 2!opSubst_pv_eq.
      rewrite -(ho_intv_subst K) -s_kind_to_sf_kind_subst -cTMemK_subst.
      (* rewrite cTMemK_subst s_kind_to_sf_kind_subst (ho_intv_subst K). *)
      iApply "Hpn".
    - rewrite -!s_kind_to_sf_kind_subst !opSubst_pv_eq.
      iApply (sstpiK_subst_oMu with "Hpn").
      iApply (narrow_sstpiK with "[] HK").
      iApply sstpiK_star_eq_sstpd.
      iApply sStp_Add_Later.
  Qed.

  (* Wrote this during discussion with Sandro; it apparently does not hold in
  the system in his thesis. *)
  Lemma sK_Sel_Red {n} Γ p l (K : s_kind Σ n) i :
    Γ s⊨p p : cTMemK l K, i -∗
    Γ s⊨ oSelN n p l ∷[i] ho_sing K (oSelN n p l).
  Proof using HswapProp. rewrite sK_Sel. apply sK_HoSing. Qed.

End derived.

Section examples.
  Context `{!dlangG Σ} `{HswapProp: SwapPropI Σ}.
  Import DBNotation dot_lty.

  Definition oId := oLam (oSel x0 "A").

  Lemma oId_K Γ :
    ⊢ Γ s⊨ oId ∷[0] sf_kpi (cTMemK "A" sf_star) sf_star.
  Proof using HswapProp. by rewrite -sK_Lam -sK_Star. Qed.
    (* Time iApply sK_Lam; iApply sK_Star. *)

  Lemma oId_K_Sngl Γ :
    ⊢ Γ s⊨ oId ∷[0] sf_kpi (cTMemK "A" sf_star) (sf_sngl (oSel x0 "A")).
  Proof using HswapProp. by rewrite -sK_Lam -sK_Sing. Qed.
End examples.

Section dot_experimental_kinds.
  Context `{!dlangG Σ} `{HswapProp: SwapPropI Σ}.

  (** As an example, we can derive this variant at an interval kind of [sSngl_Stp_Sym] *)
  Lemma sSngl_KStp_Sym Γ p q T i L U:
    Γ s⊨p p : T, i -∗ (* Just to ensure [p] terminates and [oSing p] isn't empty. *)
    Γ s⊨ oSing p <:[i] oSing q ∷ sf_kintv L U -∗
    Γ s⊨ oSing q <:[i] oSing p ∷ sf_kintv L U.
  Proof using HswapProp.
    rewrite !(sKStp_Intv_Equiv (L := L) (U := U)).
    iIntros "#Hp #(HL & Hs1 & HU)".
    iEval (rewrite sstpiK_star_eq_sstpd) in "Hs1".
    iDestruct (sSngl_Stp_Sym with "Hp Hs1") as "Hs2".
    iEval (rewrite -sstpiK_star_eq_sstpd) in "Hs1 Hs2".
    iFrame "#".
    (* iCombine "Hs Hs'" as "Hs2". *)
    iSplit.
    by iApply (sKStp_Trans with "HL Hs1").
    by iApply (sKStp_Trans with "Hs1 HU").
  Qed.

  Lemma failed_path_equality n Γ T l L U i (K : sf_kind Σ n) v w :
    Γ s⊨ T ∷[i] sf_kpi (cTMemK l (sf_kintv L U)) K -∗
    Γ s⊨ oSel v l =[i] oSel w l ∷ sf_kintv L U -∗
    Γ s⊨ oTAppV T v <:[i] oTAppV T w ∷ K.|[v/].
    (* This goal is false if T uses singleton types — say T = λ x. x.type,
    that is, [oLam (oSing (pv (ids 0)))]. *)
  Proof.
    rewrite /sstpiK.
    iIntros "/= #HT [#Hsub1 #Hsub2] !> %ρ #Hg"; iSpecialize ("HT" with "Hg");
      iSpecialize ("Hsub1" with "Hg"); iSpecialize ("Hsub2" with "Hg");
      iNext i.
    rewrite /sr_kintv/=.
    rewrite !envApply_oTAppV_eq.
    iEval asimpl.
    (* iApply sf_kind_sub_trans.
    iApply (sfkind_respects with "[] (HT [])"). *)
  Abort.


  (* WTF why am I proving this? To support more kinds? *)
  (* Make this derivable from sth. like.
  S <: T :: L..U ->
  T <: S :: * ->
  S = T :: L..U
  *)
  (* Lemma sSngl_KStp_Sym' Γ p q T i L U:
    Γ s⊨p p : T, i -∗ (* Just to ensure [p] terminates and [oSing p] isn't empty. *)
    Γ s⊨ oSing p <:[i] oSing q ∷ sf_kintv L U -∗
    Γ s⊨ oSing q <:[i] oSing p ∷ sf_kintv L U.
  Proof.
    Transparent sSkd sstpiK sstpi sptp.
    iIntros "#Hp #Hps !> %ρ #Hg /=".
    iDestruct (path_wp_eq with "(Hp Hg)") as (w) "[Hpw _] {Hp}".
    iSpecialize ("Hps" with "Hg"); rewrite -alias_paths_pv_eq_1; iNext i.
    (* Weird that this works. *)
    iDestruct ("Hps" with "Hpw") as %Hqw%alias_paths_symm.
    iDestruct "Hpw" as %Hpw.
    suff Heq: !!(envApply (oSing p) ρ ≡ envApply (oSing q) ρ)
      by iApply (sf_kind_proper with "Hps").
    iIntros (args v) "/=".
    have Hal := alias_paths_trans _ _ _ Hpw Hqw.
    by rewrite !alias_paths_pv_eq_1 (alias_paths_elim_eq_pure _ Hal).
  Qed. *)

  Program Definition kAnd (K1 K2 : sf_kind Σ 0) : sf_kind Σ 0 :=
    SfKind (λI ρ T1 T2, K1 ρ T1 T2 ∧ K2 ρ T1 T2).
  Next Obligation.
    move=> K1 K2 ρ n T1 T2 HT U1 U2 HU /=. f_equiv; exact: sf_kind_sub_ne_2.
  Qed.
  Next Obligation.
    iIntros "/= * #Heq1 #Heq2 H"; iSplitWith "H" as "H";
    iApply (sf_kind_sub_internal_proper with "Heq1 Heq2 H").
  Qed.
  Next Obligation.
    iIntros "/= * [HK1a HK2a] [HK1b HK2b]"; iSplit.
    iApply (sf_kind_sub_trans with "HK1a HK1b").
    iApply (sf_kind_sub_trans with "HK2a HK2b").
  Qed.
  Next Obligation.
    by iIntros "* [HK1 HK2]"; iSplit; iApply sf_kind_sub_quasi_refl_1.
  Qed.
  Next Obligation.
    by iIntros "* [HK1 HK2]"; iSplit; iApply sf_kind_sub_quasi_refl_2.
  Qed.

  (**
  This only checks that [T] is a _sub_singleton, not necessarily an actual
  singleton type.

  I guess that applies to Scala's Singleton, since that is modeled as an
  upper bound, but that will have to change.

  This matters for type projections!

  So if [T <: { A :: L .. U }] and [isSing T],
  then we can't conclude [▷ U <: T#A]; but if T is an actual singleton, we can.
   *)
  Definition isSing (T : lty Σ) := (□∀ v1 v2, T v1 → T v2 → ⌜ v1 = v2 ⌝)%I.

  Lemma isSing_respects_hoLty_equiv {n} {T1 T2 : hoLtyO Σ n} args:
    □ hoLty_equiv T1 T2 -∗ isSing (T1 args) -∗ isSing (T2 args).
  Proof.
    rewrite /isSing /=.
    iIntros "#Heq #HS /= !> %v1 %v2 #H1 #H2".
    iApply ("HS" with "(Heq H1) (Heq H2)").
  Qed.

  (* Uh. Not actually checking subtyping, but passes requirements. [kSing] also checks requirements. *)
  Program Definition kSing' : sf_kind Σ 0 :=
    SfKind (λI ρ T1 T2, isSing (oClose T1) ∧ isSing (oClose T2)).
  Next Obligation. rewrite /isSing/=. solve_proper_ho. Qed.

  Next Obligation.
    iIntros "* /= #Heq1 #Heq2 #Hsing"; iSplitWith "Hsing" as "Hsing'";
      iApply (isSing_respects_hoLty_equiv with "[] Hsing'");
      iIntros "!> {Hsing}"; [iApply "Heq1"|iApply "Heq2"].
  Qed.
  Next Obligation. iIntros "/= _ " (T0 T1 T2) "[$_] [_$]". Qed.
  Next Obligation. iIntros "/= _" (T1 T2) "[$ _]". Qed.
  Next Obligation. iIntros "/= _" (T1 T2) "[_ $]". Qed.

  Definition kSing (K : sf_kind Σ 0) : sf_kind Σ 0 := kAnd sf_star kSing'.
    (* SfKind (SrKind (λI ρ T1 T2, oClose T1 ⊆ oClose T2 ∧ □(∀ v1 v2, oClose T2 v1 → oClose T2 v2 → ⌜ v1 = v2 ⌝))) _ _ _ _ _. *)
End dot_experimental_kinds.
End HkDot.
