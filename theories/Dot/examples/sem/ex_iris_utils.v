(** * Infrastructure for examples of DOT programs that use Iris. *)
From D.pure_program_logic Require Import lifting adequacy.
From iris.program_logic Require Import ectxi_language.

(* Exports: *)
From D Require Export swap_later_impl.
From D.Dot Require Export skeleton.
From D.Dot Require Export ex_utils hoas_ex_utils storeless_typing_ex_utils.
From D.Dot Require Export old_fundamental examples_lr sem_unstamped_typing.
Export loopTms.

Implicit Types (v w : vl) (d : dm) (ds : dms).

Example loopDefTyp Γ : Γ v⊢ₜ hloopDefV : hloopDefT.
Proof.
  apply (iT_ISub_nocoerce hloopDefTConcr); mltcrush.
  eapply iT_All_E; last var.
  tcrush; varsub; lookup.
Qed.

Example loopFunTyp Γ : Γ v⊢ₜ hloopFunTm : ⊤ →: ⊥.
Proof. have ? := loopDefTyp Γ; tcrush. Qed.

Example loopTyp Γ : Γ v⊢ₜ hloopTm : ⊥.
Proof.
  have ? := loopFunTyp Γ; apply (iT_All_E (T1 := ⊤)), (iT_ISub_nocoerce 𝐙); tcrush.
Qed.

Ltac constrain_bisimulating :=
  hnf in *; fold same_skel_dms in *; case_match; ev; subst; try contradiction; f_equal.

Ltac unstamp_goal_tm :=
  iModIntro; iExists _; iSplit; [by iIntros "!%"; exact: same_skel_refl_tm|].
Ltac unstamp_goal_dm :=
  iModIntro; iExists _; iSplit; [by iIntros "!%"; exact: same_skel_refl_dm|].
Ltac unstamp_goal_dms :=
  iModIntro; iExists _; iSplit; [by iIntros "!%"; exact: same_skel_refl_dms|].

Section loop_sem.
  Context `{HdlangG : !dlangG Σ}.
  Context `{SwapPropI Σ}.

  Lemma loopSemT : ⊢@{iPropI _} |==> WP hclose hloopTm {{ _, False }}.
  Proof using Type*.
    iDestruct (fundamental_typed (loopTyp [])) as "#>H".
    iDestruct "H" as (e_s Hsk1) ">H"; iModIntro.
    iSpecialize ("H" $! ids with "[//]"); rewrite hsubst_id.
    move E: hloopTm => e.
    suff ->: e_s = e. { iApply (wp_wand with "H"). iIntros (v). by rw. }
    subst; clear -Hsk1. cbv; repeat constrain_bisimulating.
  Qed.

End loop_sem.

#[global] Hint Resolve not_elem_of_nil : core.
#[global] Hint Constructors NoDup : core.
