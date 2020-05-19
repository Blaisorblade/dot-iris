From D.pure_program_logic Require Import lifting adequacy.
From iris.program_logic Require Import ectxi_language.

From D Require Import swap_later_impl.
From D.Dot Require Import scala_lib hoas ex_utils storeless_typing_ex_utils.

From D.Dot Require Export fundamental.
From D.Dot Require Import skeleton.
Import dlang_adequacy.

Set Suggest Proof Using.
Set Default Proof Using "Type".

Implicit Types (v w : vl) (d : dm) (ds : dms).

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

Import hoas.syn.
Import stamp_transfer.

Section loop_sem.
  Context `{HdlangG: !dlangG Σ}.
  Context `{SwapPropI Σ}.
  Lemma loopSemT: ⊢ WP hloopTm {{ _, False }}.
  Proof using Type*.
    iDestruct (fundamental_typed (loopTyp []) with "[]") as "H".
    iApply wellMappedφ_empty.
    iSpecialize ("H" $! ids with "[//]").
    by rewrite hsubst_id /=.
  Qed.

End loop_sem.

Tactic Notation "wp_bind" uconstr(p) := iApply (wp_bind (fill [p])).
Ltac wp_pure := rewrite -wp_pure_step_later -1?wp_value; last done; iNext.

Hint Resolve not_elem_of_nil : core.
Hint Constructors NoDup : core.
