(** Auxiliary typing judgments and lemmas, shared between different variants of the typing judgment. *)
From D.Dot Require Import syn.

Set Implicit Arguments.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

Inductive un_op_syntype : un_op → base_ty → base_ty → Set :=
| ty_unot : un_op_syntype unot tbool tbool.

Inductive bin_op_syntype : bin_op → base_ty → base_ty → base_ty → Set :=
| ty_beq_bool : bin_op_syntype beq    tbool tbool tbool
| ty_beq_nat  : bin_op_syntype beq    tint  tint  tbool
| ty_blt      : bin_op_syntype blt    tint  tint  tbool
| ty_ble      : bin_op_syntype ble    tint  tint  tbool
| ty_bplus    : bin_op_syntype bplus  tint  tint  tint
| ty_btimes   : bin_op_syntype btimes tint  tint  tint.

(** * When is a context weaker than another? While we don't give complete
rules, we develop some infrastructure to allow "stripping" laters from the
context. *)

Reserved Notation "⊢G Γ1 <:* Γ2" (at level 74, Γ1, Γ2 at next level).
Reserved Notation "⊢T T1 <: T2" (at level 74, T1, T2 at next level).

Reserved Notation "⊢G G1 '>>▷*' G2" (at level 74, G1, G2 at next level).
Reserved Notation "⊢T T1 '>>▷' T2" (at level 74, T1, T2 at next level).

(** A left inverse of TLater. Sometimes written ⊲. *)
(* Definition unTLater T : ty := match T with | TLater T' => T' | _ => T end. *)
Fixpoint unTLater T : ty := match T with
| TLater T' => T'
| TAnd T1 T2 => TAnd (unTLater T1) (unTLater T2)
| TOr T1 T2 => TOr (unTLater T1) (unTLater T2)
| _ => T
end.

Definition unTLater_TLater T: unTLater (TLater T) = T := reflexivity _.
Global Instance: Cancel (=) unTLater TLater. Proof. exact: unTLater_TLater. Qed.

Inductive ty_strip_syn : ty → ty → Prop :=
| ty_strip_id_syn T : ⊢T T >>▷ T
| ty_strip_TLater_add_syn T :
  ⊢T TLater T >>▷ T
| ty_strip_cong_TAnd_syn T1 T2 U1 U2 :
  ⊢T T1 >>▷ U1 → ⊢T T2 >>▷ U2 → ⊢T TAnd T1 T2 >>▷ TAnd U1 U2
| ty_strip_cong_TOr_syn T1 T2 U1 U2 :
  ⊢T T1 >>▷ U1 → ⊢T T2 >>▷ U2 → ⊢T TOr T1 T2 >>▷ TOr U1 U2
| ty_strip_cong_TLater_syn T1 T2 :
  ⊢T T1 >>▷ T2 →
  ⊢T TLater T1 >>▷ TLater T2
where "⊢T T1 '>>▷' T2" := (ty_strip_syn T1 T2).
Hint Constructors ty_strip_syn : ctx_sub.

(** The actual constructor is [ty_sub_TLater_syn]; the other ones are
just congruence under [TLater], [TAnd], [TOr].
We also add transitivity: it is not admissible, and the counterexample is
[⊢T T <: TLater (TLater T)]. *)
Inductive ty_sub_syn : ty → ty → Prop :=
| ty_sub_id_syn T : ⊢T T <: T
| ty_trans_sub_syn T1 T2 T3 :
  ⊢T T1 <: T2 → ⊢T T2 <: T3 → ⊢T T1 <: T3
| ty_sub_TLater_add_syn T1 T2 :
  ⊢T T1 <: T2 → ⊢T T1 <: TLater T2
| ty_sub_cong_TAnd_syn T1 T2 U1 U2 :
  ⊢T T1 <: U1 → ⊢T T2 <: U2 → ⊢T TAnd T1 T2 <: TAnd U1 U2
| ty_sub_cong_TOr_syn T1 T2 U1 U2 :
  ⊢T T1 <: U1 → ⊢T T2 <: U2 → ⊢T TOr T1 T2 <: TOr U1 U2
| ty_sub_cong_TLater_syn T1 T2 :
  ⊢T T1 <: T2 →
  ⊢T TLater T1 <: TLater T2
(* | ty_swap_later_and T1 T2 :
  ⊢T TLater (TAnd T1 T2) <: TAnd (TLater T1) (TLater T2) *)
| ty_distr_TAnd_TLater_syn T1 T2 :
  ⊢T TAnd (TLater T1) (TLater T2) <: TLater (TAnd T1 T2)
| ty_distr_TOr_TLater_syn T1 T2 :
  ⊢T TOr (TLater T1) (TLater T2) <: TLater (TOr T1 T2)
(* Unused: *)
(* | ty_sub_TLater_unTLater_syn T :
  ⊢T T <: TLater (unTLater T). *)
where "⊢T T1 <: T2" := (ty_sub_syn T1 T2).
Hint Constructors ty_sub_syn : ctx_sub.

(** Control transitivity to ensure [eauto] does not diverge. *)
Remove Hints ty_trans_sub_syn : ctx_sub.
Hint Extern 5 (⊢T _ <: _) => try_once ty_trans_sub_syn : ctx_sub.

Lemma ty_sub_TLater_syn T : ⊢T T <: TLater T. Proof. auto with ctx_sub. Qed.
Hint Resolve ty_sub_TLater_syn : ctx_sub.

Lemma ty_strip_to_sub T1 T2 :
  ⊢T T1 >>▷ T2 →
  ⊢T T1 <: TLater T2.
Proof. induction 1; eauto with ctx_sub. Qed.

Lemma unTLater_ty_sub_syn T : ⊢T unTLater T <: T.
Proof. induction T; cbn; auto with ctx_sub. Qed.
(* Not so easy to prove? *)
(* Lemma ty_sub_TLater_unTLater_syn T :
  ⊢T T <: TLater (unTLater T).
Proof.
  induction T; cbn; auto with ctx_sub.
Abort. *)

Hint Resolve unTLater_ty_sub_syn : ctx_sub.

Inductive ctx_strip_syn : ctx → ctx → Prop :=
| ctx_strip_nil_syn : ⊢G [] >>▷* []
| ctx_strip_cons_syn T1 T2 Γ1 Γ2 :
  ⊢T T1 >>▷ T2 →
  ⊢G Γ1 >>▷* Γ2 →
  ⊢G T1 :: Γ1 >>▷* T2 :: Γ2
where "⊢G Γ1 >>▷* Γ2" := (ctx_strip_syn Γ1 Γ2).
Hint Constructors ctx_strip_syn : ctx_sub.

Lemma ctx_strip_id_syn Γ : ⊢G Γ >>▷* Γ.
Proof. elim: Γ => //=; auto with ctx_sub. Qed.

Hint Resolve ctx_strip_id_syn : ctx_sub.

Inductive ctx_sub_syn : ctx → ctx → Prop :=
| ctx_sub_nil_syn : ⊢G [] <:* []
| ctx_sub_cons_syn T1 T2 Γ1 Γ2 :
  ⊢T T1 <: T2 →
  ⊢G Γ1 <:* Γ2 →
  ⊢G T1 :: Γ1 <:* T2 :: Γ2
where "⊢G Γ1 <:* Γ2" := (ctx_sub_syn Γ1 Γ2).
Hint Constructors ctx_sub_syn : ctx_sub.

Lemma ctx_sub_id_syn Γ : ⊢G Γ <:* Γ.
Proof. induction Γ; auto with ctx_sub. Qed.

Lemma ctx_sub_trans_sub_syn Γ1 Γ2 Γ3 :
  ⊢G Γ1 <:* Γ2 → ⊢G Γ2 <:* Γ3 → ⊢G Γ1 <:* Γ3.
Proof.
  move: Γ1 => + + Hsub2.
  induction Hsub2; inversion 1; subst; eauto with ctx_sub.
Qed.

Lemma ctx_strip_to_sub G1 G2 :
  ⊢G G1 >>▷* G2 →
  ⊢G G1 <:* TLater <$> G2.
Proof. elim=> /=; eauto using ty_strip_to_sub with ctx_sub. Qed.

Lemma fmap_ctx_sub_syn {Γ} (f g : ty → ty):
  (∀ T, ⊢T f T <: g T) →
  ⊢G f <$> Γ <:* g <$> Γ.
Proof. induction Γ; cbn; auto with ctx_sub. Qed.

Lemma unTLater_ctx_sub_syn Γ :
  ⊢G unTLater <$> Γ <:* Γ.
Proof.
  rewrite -{2}(map_id Γ).
  apply (fmap_ctx_sub_syn _ id); auto with ctx_sub.
Qed.

Lemma ctx_sub_TLater_syn Γ :
  ⊢G Γ <:* TLater <$> Γ.
Proof.
  rewrite -{1}(map_id Γ).
  apply (fmap_ctx_sub_syn id _); auto with ctx_sub.
Qed.

(* | ctx_sub_TLater_unTLater_syn Γ :
  ⊢G Γ <:* TLater <$> (unTLater <$> Γ) *)
Lemma TLater_cong_ctx_sub_syn Γ1 Γ2 :
  ⊢G Γ1 <:* Γ2 →
  ⊢G TLater <$> Γ1 <:* TLater <$> Γ2.
Proof. induction 1; cbn; auto with ctx_sub. Qed.

Hint Resolve ctx_sub_id_syn ctx_sub_trans_sub_syn unTLater_ctx_sub_syn
  ctx_sub_TLater_syn TLater_cong_ctx_sub_syn : ctx_sub.

Ltac ietp_weaken_ctx := auto with ctx_sub.

Lemma ctx_sub_len Γ Γ' : ⊢G Γ <:* Γ' → length Γ = length Γ'.
Proof. by elim => [|> ?? /= ->]. Qed.

Lemma ctx_sub_len_tlater {Γ Γ'} : ⊢G Γ <:* TLater <$> Γ' → length Γ = length Γ'.
Proof. intros ->%ctx_sub_len. apply fmap_length. Qed.

Lemma ctx_strip_len Γ Γ' : ⊢G Γ >>▷* Γ' → length Γ = length Γ'.
Proof. by elim => [|> ?? /= ->]. Qed.
