(** * Infrastructure for examples of DOT programs that use Iris. *)
From D.pure_program_logic Require Import lifting adequacy.
From iris.program_logic Require Import ectxi_language.

From D Require Import swap_later_impl.
From D.Dot Require Import skeleton stampedness_binding.

(* Exports: *)
From D.Dot Require Export ex_utils hoas_ex_utils storeless_typing_ex_utils.
From D.Dot Require Export old_fundamental examples_lr.
Export loopTms.

Set Suggest Proof Using.
Set Default Proof Using "Type".

Implicit Types (v w : vl) (d : dm) (ds : dms) (T : ty).

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

Ltac constrain_bisimulating :=
  hnf in *; fold same_skel_dms in *; case_match; ev; subst; try contradiction; f_equal.

Section loop_sem.
  Context `{HdlangG: !dlangG Σ}.
  Context `{SwapPropI Σ}.

  Definition cTMemL l L U := cTMem l (oLater L) (oLater U).

  Lemma loopSemT: ⊢ WP hloopTm {{ _, False }}.
  Proof using Type*.
    iDestruct (fundamental_typed (loopTyp [])) as "#>H".
    iDestruct "H" as (e_s Hsk1) "H".
    iSpecialize ("H" $! ids with "[//]"); rewrite hsubst_id.
    move E: hloopTm =>e; suff <-: e_s = e by []; subst; clear -Hsk1.
    cbv; repeat constrain_bisimulating.
  Qed.

End loop_sem.

Tactic Notation "wp_bind" uconstr(p) := iApply (wp_bind (fill [p])).
Ltac wp_pure := rewrite -wp_pure_step_later -1?wp_value; last done; iNext.

Hint Resolve not_elem_of_nil : core.
Hint Constructors NoDup : core.

Module stamp_transfer.
Section sem.
  Context `{Hdlang : !dlangG Σ}.
  Implicit Types (s : stamp) (gφ : gmap stamp (hoEnvD Σ 0)).

  Definition wellMappedφ gφ : iProp Σ :=
    □∀ s φ (Hl : gφ !! s = Some φ), s ↝n[ 0 ] φ.
  Global Instance wellMappedφ_persistent gφ: Persistent (wellMappedφ gφ) := _.

  Lemma wellMappedφ_empty : ⊢ wellMappedφ ∅. Proof. by iIntros (???). Qed.

  Lemma wellMappedφ_insert gφ s φ :
    wellMappedφ gφ -∗ s ↝n[ 0 ] φ -∗ wellMappedφ (<[s:=φ]> gφ).
  Proof.
    iIntros "#Hwmg #Hs !>" (s' φ' Hl). case: (decide (s' = s)) Hl => [->|?];
      rewrite (lookup_insert, lookup_insert_ne) => ?;
      simplify_eq; by [> iApply "Hs" | iApply "Hwmg"].
  Qed.

  Lemma wellMappedφ_apply s φ gφ : gφ !! s = Some φ → wellMappedφ gφ -∗ s ↝n[ 0 ] φ.
  Proof. iIntros (Hl) "#Hm"; iApply ("Hm" $! _ _ Hl). Qed.

  Lemma wellMappedφ_extend gφ1 gφ2 (Hle : gφ2 ⊆ gφ1):
      wellMappedφ gφ1 -∗ wellMappedφ gφ2.
  Proof.
    iIntros "#Hs" (s φ Hl) "/= !>". iApply ("Hs" with "[%]").
    by eapply map_subseteq_spec, Hl.
  Qed.

  Global Opaque wellMappedφ.

  Lemma extraction_to_leadsto_envD_equiv T g s σ n : T ~[ n ] (g, (s, σ)) →
    wellMappedφ Vs⟦ g ⟧ -∗ s ↝[ σ ] V⟦ T ⟧.
  Proof.
    move => [T'] [Hl] [<- [_ /is_stamped_nclosed_ty HclT]].
    iIntros "Hm". iExists V⟦ T' ⟧. iSplitR.
    - iIntros "!%" (args ρ v). exact: interp_finsubst_commute_cl.
    - iApply (wellMappedφ_apply with "Hm"). by rewrite lookup_fmap Hl.
  Qed.
End sem.

(** Judgment variants indexed by [gφ]. *)
Notation "Γ ⊨[ gφ  ] { l := d  } : T" := (wellMappedφ gφ → idtp Γ T l d)%I (at level 74, d, l, T at next level).
Notation "Γ ⊨ds[ gφ  ] ds : T" := (wellMappedφ gφ → idstp Γ T ds)%I (at level 74, ds, T at next level).
Notation "Γ ⊨[ gφ  ] e : T" := (wellMappedφ gφ → ietp Γ T e)%I (at level 74, e, T at next level).
Notation "Γ ⊨p[ gφ  ] p : T , i" := (wellMappedφ gφ → iptp Γ T p i)%I (at level 74, p, T, i at next level).
Notation "Γ ⊨[ gφ  ] T1 , i <: T2 , j" := (wellMappedφ gφ → istpi Γ T1 T2 i j)%I (at level 74, T1, T2, i, j at next level).
Notation "Γ ⊨[ gφ  ] T1 <:[ i  ] T2 " := (wellMappedφ gφ → istpd i Γ T1 T2)%I (at level 74, T1, T2, i at next level).

End stamp_transfer.
