From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

From D Require Import swap_later_impl proper.
From D.Dot Require Import rules unary_lr.

Reserved Notation "⊢G Γ1 <:* Γ2" (at level 74, Γ1, Γ2 at next level).
Reserved Notation "⊢T T1 <: T2" (at level 74, T1, T2 at next level).

Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms) (ρ : env).

(* TODO: all of this, minus unTLater, can be generalized to semantic types/contexts. *)

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

(** The actual constructor is [ty_sub_TLater_syn]; the other ones are
just congruence under [TLater], [TAnd], [TOr].
We also add transitivity: it is not admissible, and the counterexample is
[⊢T T <: TLater (TLater T)]. *)
Inductive ty_sub_syn : ty → ty → Prop :=
| ty_sub_id_syn T : ⊢T T <: T
| ty_sub_TLater_add_syn T1 T2 :
  ⊢T T1 <: T2 → ⊢T T1 <: TLater T2
| ty_sub_cong_TAnd_syn T1 T2 U1 U2 :
  ⊢T T1 <: U1 → ⊢T T2 <: U2 → ⊢T TAnd T1 T2 <: TAnd U1 U2
| ty_sub_cong_TOr_syn T1 T2 U1 U2 :
  ⊢T T1 <: U1 → ⊢T T2 <: U2 → ⊢T TOr T1 T2 <: TOr U1 U2
| ty_sub_cong_TLater_syn T1 T2 :
  ⊢T T1 <: T2 →
  ⊢T TLater T1 <: TLater T2
(* Unused: *)
(* | ty_sub_TLater_unTLater_syn T :
  ⊢T T <: TLater (unTLater T). *)
where "⊢T T1 <: T2" := (ty_sub_syn T1 T2).
Hint Constructors ty_sub_syn : ctx_sub.

Lemma ty_sub_TLater_syn T : ⊢T T <: TLater T. Proof. auto with ctx_sub. Qed.

Lemma ty_trans_sub_syn T1 T2 T3 : ⊢T T1 <: T2 → ⊢T T2 <: T3 → ⊢T T1 <: T3.
Proof.
  move => + Hsub2. move: T1.
  induction Hsub2; inversion 1; subst; auto with ctx_sub.
Qed.

Hint Resolve ty_sub_TLater_syn ty_trans_sub_syn : ctx_sub.

Lemma unTLater_ty_sub_syn T : ⊢T unTLater T <: T.
Proof. induction T; cbn; auto with ctx_sub. Qed.
(* Not so easy to prove? *)
(* Lemma ty_sub_TLater_unTLater_syn T :
  ⊢T T <: TLater (unTLater T).
Proof.
  induction T; cbn; auto with ctx_sub.
Abort. *)

Hint Resolve unTLater_ty_sub_syn : ctx_sub.

Inductive ctx_sub_syn : ctx → ctx → Prop :=
| ctx_sub_nil_syn : ⊢G [] <:* []
(* | ctx_sub_TLater_unTLater_syn Γ :
  ⊢G Γ <:* TLater <$> (unTLater <$> Γ) *)
| ctx_sub_cons_syn T1 T2 Γ1 Γ2 :
  ⊢T T1 <: T2 →
  ⊢G Γ1 <:* Γ2 →
  ⊢G T1 :: Γ1 <:* T2 :: Γ2
where "⊢G Γ1 <:* Γ2" := (ctx_sub_syn Γ1 Γ2).
Hint Constructors ctx_sub_syn : ctx_sub.

Lemma ctx_id_syn Γ : ⊢G Γ <:* Γ.
Proof. induction Γ; auto with ctx_sub. Qed.

Lemma ctx_trans_sub_syn Γ1 Γ2 Γ3 :
  ⊢G Γ1 <:* Γ2 → ⊢G Γ2 <:* Γ3 → ⊢G Γ1 <:* Γ3.
Proof.
  move => + Hsub2. move: Γ1.
  induction Hsub2; inversion 1; subst; eauto with ctx_sub.
Qed.

Lemma fmap_ctx_sub_syn {Γ} (f g : ty -> ty):
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

Hint Resolve ctx_id_syn ctx_trans_sub_syn unTLater_ctx_sub_syn
  ctx_sub_TLater_syn TLater_cong_ctx_sub_syn : ctx_sub.

(** * When is a context weaker than another? While we don't give complete
rules, we develop some infrastructure to allow "stripping" laters from the
context. *)
(* This is specialized to [vnil] because contexts only contain proper types anyway. *)
Definition ty_sub `{HdlangG: dlangG Σ} T1 T2 := ∀ ρ v, V⟦ T1 ⟧ vnil ρ v -∗ V⟦ T2 ⟧ vnil ρ v.
Notation "⊨T T1 <: T2" := (ty_sub T1 T2) (at level 74, T1, T2 at next level).
Typeclasses Opaque ty_sub.

Definition ctx_sub `{HdlangG: dlangG Σ} Γ1 Γ2 : Prop := ∀ ρ, G⟦ Γ1 ⟧ ρ -∗ G⟦ Γ2 ⟧ ρ.
Notation "⊨G Γ1 <:* Γ2" := (ctx_sub Γ1 Γ2) (at level 74, Γ1, Γ2 at next level).
Typeclasses Opaque ctx_sub.

Section CtxSub.
  Context `{HdlangG: dlangG Σ}.
  Implicit Type (T : ty) (Γ : ctx).

  (** * Basic lemmas about [ctx_sub]. *)
  (* TODO: Make this into a structural typing rule? *)
  Global Instance: RewriteRelation ty_sub := {}.
  Global Instance: PreOrder ty_sub.
  Proof. split. by move => ??. by move => x y z H1 H2 ρ v; rewrite (H1 _ _). Qed.

  Global Instance: RewriteRelation ctx_sub := {}.
  Global Instance: PreOrder ctx_sub.
  Proof. split. by move => ??. by move => x y z H1 H2 ρ; rewrite (H1 _). Qed.

  Global Instance Proper_cons_ctx_sub : Proper (ty_sub ==> ctx_sub ==> ctx_sub) cons.
  Proof. move => T1 T2 HlT Γ1 Γ2 Hl ρ. cbn. by rewrite (HlT _) (Hl _). Qed.

  Global Instance Proper_cons_ctx_sub_flip : Proper (flip ty_sub ==> flip ctx_sub ==> flip ctx_sub) cons.
  Proof. solve_proper. Qed.

  (** Typing is contravariant in [Γ]. *)
  Global Instance Proper_ietp : Proper (flip ctx_sub ==> (=) ==> (=) ==> (⊢)) ietp.
  Proof. rewrite /ietp /= => Γ1 Γ2 Hweak ??????; subst. by setoid_rewrite (Hweak _). Qed.
  Global Instance Proper_ietp_flip :
    Proper (ctx_sub ==> flip (=) ==> flip (=) ==> flip (⊢)) ietp.
  Proof. apply flip_proper_4, Proper_ietp. Qed.

  Global Instance Proper_TLater : Proper (ty_sub ==> ty_sub) TLater.
  Proof. intros x y Hl ??. by rewrite /= (Hl _ _). Qed.
  Global Instance Proper_TLater_flip :
    Proper (flip ty_sub ==> flip ty_sub) TLater.
  Proof. apply: flip_proper_2. Qed.

  Lemma senv_TLater_commute (Γ : sCtx Σ) ρ : s⟦ oLater <$> Γ ⟧* ρ ⊣⊢ ▷ s⟦ Γ ⟧* ρ.
  Proof.
    elim: Γ ρ => [| T Γ IH] ρ; cbn; [|rewrite IH later_and];
      iSplit; by [iIntros "$" | iIntros "_"].
  Qed.

  Lemma fmap_TLater_oLater Γ : V⟦ TLater <$> Γ ⟧* ≡ oLater <$> V⟦ Γ ⟧*.
  Proof. elim: Γ => [//| T Γ IH]; cbn. by rewrite IH. Qed.

  Lemma env_TLater_commute Γ ρ : G⟦ TLater <$> Γ ⟧ ρ ⊣⊢ ▷ G⟦ Γ ⟧ ρ.
  Proof. by rewrite -senv_TLater_commute fmap_TLater_oLater. Qed.

  (** The strength ordering of contexts lifts the strength ordering of types. *)
  Lemma env_lift_sub f g {Γ} (Hle: ∀ T, ⊨T f T <: g T):
    ⊨G f <$> Γ <:* g <$> Γ.
  Proof. elim: Γ => [//| T Γ IH] ρ; cbn. by rewrite (Hle T _ _) -(IH _). Qed.

  Lemma env_lift_sub' f g Γ {Γ1 Γ2}:
    Γ1 = f <$> Γ → Γ2 = g <$> Γ →
    (∀ T, ⊨T f T <: g T) →
    ⊨G Γ1 <:* Γ2.
  Proof. move => -> -> Hweak. exact: env_lift_sub. Qed.

  (* It's not immediate to generalize Proper_fmap_TLater to [fmap C] for a
  type constructor [C]. Fpr instance, the following is hopeless. *)
  (* Lemma Proper_fmap_ctx C
    (Hle: ∀ T1 T2, ⊨T T1 <: T2 → ⊨T C T1 <: C T2):
    Proper (ctx_sub ==> ctx_sub) (fmap C).
  Proof.
    intros G1 G2. elim: G2 G1 => [|T2 G2 IHG2] [|T1 G1] HG ρ //; cbn. *)

  Global Instance Proper_fmap_TLater :
    Proper (ctx_sub ==> ctx_sub) (fmap TLater).
  Proof. intros xs ys Hl ?. by rewrite !env_TLater_commute (Hl _). Qed.
  Global Instance Proper_fmap_TLater_flip :
    Proper (flip ctx_sub ==> flip ctx_sub) (fmap TLater).
  Proof. apply: flip_proper_2. Qed.

  Global Instance Proper_TAnd : Proper (ty_sub ==> ty_sub ==> ty_sub) TAnd.
  Proof. intros x y Hl x' y' Hl' ??. by rewrite /= (Hl _ _) (Hl' _ _). Qed.
  Global Instance Proper_TAnd_flip :
    Proper (flip ty_sub ==> flip ty_sub ==> flip ty_sub) TAnd.
  Proof. apply: flip_proper_3. Qed.

  Global Instance Proper_TOr : Proper (ty_sub ==> ty_sub ==> ty_sub) TOr.
  Proof. intros x y Hl x' y' Hl' ??. by rewrite /= (Hl _ _) (Hl' _ _). Qed.
  Global Instance Proper_TOr_flip :
    Proper (flip ty_sub ==> flip ty_sub ==> flip ty_sub) TOr.
  Proof. apply: flip_proper_3. Qed.

  (** Ordering of logical strength:
      unTLater T <: T <: TLater (unTLater T) <: TLater T. *)
  Lemma unTLater_ty_sub T : ⊨T unTLater T <: T.
  Proof. induction T => //=; by [ f_equiv | intros ?; auto ]. Qed.

  Lemma ty_sub_TLater_unTLater T : ⊨T T <: TLater (unTLater T).
  Proof.
    induction T; try by [iIntros (??) "$"];
      rewrite {1}IHT1 {1}IHT2 /=; intros ??;
      [> iIntros "[$ $]" | iIntros "[$|$]"].
  Qed.

  Lemma ty_sub_id T : ⊨T T <: T. Proof. done. Qed.

  Lemma ty_sub_TLater T : ⊨T T <: TLater T.
  Proof. intros ?. auto. Qed.

  Lemma ty_sub_TLater_add T1 T2 :
    ⊨T T1 <: T2 →
    ⊨T T1 <: TLater T2.
  Proof. intros ->. apply ty_sub_TLater. Qed.

  Hint Resolve ty_sub_id ty_sub_TLater ty_sub_TLater_add ty_sub_TLater_unTLater unTLater_ty_sub : ctx_sub.

  (* Unused *)
  Lemma TLater_unTLater_ty_sub_TLater T :
    ⊨T TLater (unTLater T) <: TLater T.
  Proof. by rewrite unTLater_ty_sub. Qed.

  Lemma fundamental_ty_sub {T1 T2} : ⊢T T1 <: T2 → ⊨T T1 <: T2.
  Proof. induction 1; auto with f_equiv ctx_sub. Qed.
  Hint Resolve fundamental_ty_sub : ctx_sub.

  (** Lift the above ordering to environments. *)

  Lemma ctx_sub_nil : ⊨G [] <:* []. Proof. done. Qed.

  Lemma unTLater_ctx_sub Γ : ⊨G unTLater <$> Γ <:* Γ.
  Proof. eapply env_lift_sub', unTLater_ty_sub; by rewrite ?list_fmap_id. Qed.

  Lemma ctx_sub_TLater Γ : ⊨G Γ <:* TLater <$> Γ.
  Proof. eapply env_lift_sub', ty_sub_TLater; by rewrite ?list_fmap_id. Qed.

  Lemma ctx_sub_TLater_unTLater Γ : ⊨G Γ <:* TLater <$> (unTLater <$> Γ).
  Proof.
    rewrite -list_fmap_compose.
    eapply env_lift_sub', ty_sub_TLater_unTLater; by rewrite ?list_fmap_id.
  Qed.

  Hint Resolve ctx_sub_nil ctx_sub_TLater ctx_sub_TLater_unTLater unTLater_ctx_sub : ctx_sub.

  Lemma fundamental_ctx_sub {Γ1 Γ2} : ⊢G Γ1 <:* Γ2 → ⊨G Γ1 <:* Γ2.
  Proof. induction 1; auto with f_equiv ctx_sub. Qed.

  Local Hint Resolve fundamental_ctx_sub : ctx_sub.

  Lemma ctx_sub_cons_id_syn T Γ1 Γ2 :
    ⊢G Γ1 <:* Γ2 → ⊢G T :: Γ1 <:* T :: Γ2.
  Proof. auto with ctx_sub. Qed.

  Lemma ctx_sub_cons_later_syn T Γ1 Γ2 :
    ⊢G Γ1 <:* Γ2 → ⊢G T :: Γ1 <:* TLater T :: Γ2.
  Proof. auto with ctx_sub. Qed.

  Lemma ctx_sub_cons_later T Γ1 Γ2 (Hle : ⊨G Γ1 <:* Γ2) :
    ⊨G T :: Γ1 <:* TLater T :: Γ2.
  Proof. auto with f_equiv ctx_sub. Qed.

  Lemma TLater_unTLater_TLater_ctx_sub_syn Γ :
    ⊢G TLater <$> (unTLater <$> Γ) <:* TLater <$> Γ.
  Proof. auto with ctx_sub. Qed.

  (* Unused *)
  Lemma TLater_unTLater_TLater_ctx_sub Γ :
    ⊨G TLater <$> (unTLater <$> Γ) <:* TLater <$> Γ.
  (* Proof. by rewrite unTLater_ctx_sub. Qed. *)
  Proof. auto with ctx_sub. Qed.

  Lemma ietp_weaken_ctx_syn Γ1 Γ2 {T e} (Hsyn : ⊢G Γ1 <:* Γ2) : Γ2 ⊨ e : T -∗ Γ1 ⊨ e : T.
  Proof. by apply Proper_ietp; first apply (fundamental_ctx_sub Hsyn). Qed.
End CtxSub.

Hint Resolve ietp_weaken_ctx_syn : ctx_sub.
Ltac ietp_weaken_ctx := auto with ctx_sub.

Section LambdaIntros.
  Context `{HdlangG: dlangG Σ}.

  Lemma sT_All_I_Strong {Γ} T1 T2 e:
    shift T1 :: Γ s⊨ e : T2 -∗
    (*─────────────────────────*)
    oLater <$> Γ s⊨ tv (vabs e) : oAll T1 T2.
  Proof.
    iIntros "#HeT !>" (ρ) "#HG /= !>".
    rewrite -wp_value'. iExists _; iSplit; first done.
    iIntros "!>" (v) "#Hv"; rewrite up_sub_compose.
    (* Factor ▷ out of [s⟦ Γ ⟧* ρ] before [iNext]. *)
    rewrite senv_TLater_commute.
    iNext.
    iApply ("HeT" $! (v .: ρ) with "[$HG]").
    by rewrite (hoEnvD_weaken_one T1 vnil _ v) stail_eq.
  Qed.

  Lemma sT_All_I {Γ} T1 T2 e:
    shift T1 :: Γ s⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ s⊨ tv (vabs e) : oAll T1 T2.
  Proof.
    rewrite sT_All_I_Strong.
    iIntros "#HeT !>" (ρ) "#HG /= !>".
    iApply ("HeT" $! ρ with "[]").
    rewrite senv_TLater_commute. iApply "HG".
  Qed.

  Lemma T_All_I_Strong {Γ} T1 T2 e:
    shift T1 :: (unTLater <$> Γ) ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    rewrite /ietp/setp fmap_cons.
    setoid_rewrite (ctx_sub_TLater_unTLater Γ _).
    setoid_rewrite (fmap_TLater_oLater _).
    setoid_rewrite (pty_interp_subst T1 (ren (+1))).
    apply (sT_All_I_Strong (Γ := V⟦unTLater <$> Γ⟧*) V⟦T1⟧ V⟦T2⟧ e).
  Qed.

  (* Derivable *)
  Lemma T_All_I {Γ} T1 T2 e:
    shift T1 :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  (* Proof. by rewrite -T_All_I_Strong (unTLater_ctx_sub Γ). Qed. *)
  Proof.
    rewrite -T_All_I_Strong. ietp_weaken_ctx.
    (* Restart.
    by rewrite /ietp -sT_All_I fmap_cons (pty_interp_subst T1 (ren (+1))). *)
  Qed.

  Lemma sP_Val {Γ} v T:
    Γ s⊨ tv v : T -∗
    Γ s⊨p pv v : T, 0.
  Proof.
    iIntros "/= #Hp !>" (ρ) "Hg"; iSpecialize ("Hp" with "Hg").
    by rewrite /= wp_value_inv' path_wp_pv.
  Qed.

  Lemma P_Val {Γ} v T: Γ ⊨ tv v : T -∗ Γ ⊨p pv v : T, 0.
  Proof. apply sP_Val. Qed.

  (** Lemmas about definition typing. *)
  Lemma sD_Path_TVMem_I {Γ} T p l:
    Γ s⊨p p : T, 0 -∗
    Γ s⊨ { l := dpt p } : oLDVMem l T.
  Proof.
    iIntros "/= #Hv !>" (ρ Hpid) "#Hg".
    rewrite def_interp_tvmem_eq.
    iApply ("Hv" with "Hg").
  Qed.

  Lemma D_Path_TVMem_I {Γ} T p l:
    Γ ⊨p p : T, 0 -∗ Γ ⊨ { l := dpt p } : TVMem l T.
  Proof. apply sD_Path_TVMem_I. Qed.

  Lemma sD_TVMem_I {Γ} T v l:
    Γ s⊨ tv v : T -∗
    Γ s⊨ { l := dpt (pv v) } : oLDVMem l T.
  Proof. by rewrite -sD_Path_TVMem_I -sP_Val. Qed.

  Lemma D_TVMem_I {Γ} T v l:
    Γ ⊨ tv v : T -∗ Γ ⊨ { l := dpt (pv v) } : TVMem l T.
  Proof. apply sD_TVMem_I. Qed.

  (* Derivable, to drop. *)
  Lemma D_TVMem_All_I_Strong {Γ} T1 T2 e l:
    shift T1 :: (unTLater <$> Γ) ⊨ e : T2 -∗
    Γ ⊨ { l := dpt (pv (vabs e)) } : TVMem l (TAll T1 T2).
  Proof. by rewrite -D_TVMem_I -T_All_I_Strong. Qed.

  Lemma D_TVMem_All_I {Γ} V T1 T2 e l:
    shift T1 :: V :: Γ ⊨ e : T2 -∗
    Γ |L V ⊨ { l := dpt (pv (vabs e)) } : TVMem l (TAll T1 T2).
  Proof.
    (* Compared to [T_All_I], we must strip later also from [TLater V]. *)
    rewrite -D_TVMem_All_I_Strong fmap_cons cancel.
    ietp_weaken_ctx.
  Qed.
End LambdaIntros.

Section Sec.
  Context `{HdlangG: dlangG Σ}.

  Lemma sT_Sub {Γ e T1 T2 i}:
    Γ s⊨ e : T1 -∗
    Γ s⊨ T1, 0 <: T2, i -∗
    (*───────────────────────────────*)
    Γ s⊨ iterate tskip i e : T2.
  Proof.
    iIntros "/= #HeT1 #Hsub !>" (ρ) "#Hg !>".
    rewrite tskip_subst -wp_bind.
    iApply (wp_wand with "(HeT1 Hg)").
    iIntros (v) "#HvT1".
    (* We can swap ▷^i with WP (tv v)! *)
    rewrite -wp_pure_step_later // -wp_value.
    by iApply "Hsub".
  Qed.

  Lemma T_Sub {Γ e T1 T2 i}:
    Γ ⊨ e : T1 -∗ Γ ⊨ T1, 0 <: T2, i -∗ Γ ⊨ iterate tskip i e : T2.
  Proof. apply sT_Sub. Qed.

  (*
     x ∉ fv T
     ----------------------------------------------- (<:)
     Γ ⊨ mu x: T <: T    Γ ⊨ T <: mu(x: T)
  *)

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂ᶻ
     ----------------------------------------------- (<:-μ-X)
     Γ ⊨ μ (x: T₁ˣ) <: μ(x: T₂ˣ)
  *)
  Lemma sSub_Mu_X {Γ T1 T2 i j} :
    iterate oLater i T1 :: Γ s⊨ T1, i <: T2, j -∗
    Γ s⊨ oMu T1, i <: oMu T2, j.
  Proof.
    iIntros "/= #Hstp !>" (vs v) "#Hg #HT1".
    iApply ("Hstp" $! (v .: vs) v with "[# $Hg] [#//]").
    by rewrite iterate_oLater_later.
  Qed.

  (* Novel subtyping rules. sSub_Mu_1 and sSub_Mu_2 become (sort-of?)
  derivable. *)
  Lemma sSub_Mu_A {Γ T i} : Γ s⊨ oMu (shift T), i <: T, i.
  Proof. iIntros "!> **". by rewrite s_interp_TMu_ren. Qed.

  Lemma sSub_Mu_B {Γ T i} : Γ s⊨ T, i <: oMu (shift T), i.
  Proof. iIntros "!> **". by rewrite s_interp_TMu_ren. Qed.

  (*
     Γ ⊨ z: Tᶻ
     =============================================== (T-Rec-I/T-Rec-E)
     Γ ⊨ z: mu(x: Tˣ)
   *)
  Lemma sTMu_equiv {Γ T v} : (Γ s⊨ tv v : oMu T) ≡ (Γ s⊨ tv v : T.|[v/]).
  Proof.
    iSplit; iIntros "#Htp !>" (vs) "#Hg !> /=";
    iDestruct (wp_value_inv' with "(Htp Hg)") as "{Htp} Hgoal";
    rewrite -wp_value/= (hoEnvD_subst_one _ v (v.[vs])); done.
  Qed.

  Lemma sT_Mu_I {Γ T v} : Γ s⊨ tv v : T.|[v/] -∗ Γ s⊨ tv v : oMu T.
  Proof. by rewrite sTMu_equiv. Qed.

  Lemma sT_Mu_E {Γ T v} : Γ s⊨ tv v : oMu T -∗ Γ s⊨ tv v : T.|[v/].
  Proof. by rewrite sTMu_equiv. Qed.

  Lemma Sub_Mu_X {Γ} T1 T2 i j:
    iterate TLater i T1 :: Γ ⊨ T1, i <: T2, j -∗
    Γ ⊨ TMu T1, i <: TMu T2, j.
  Proof.
    rewrite /istpi -sSub_Mu_X.
    by rewrite fmap_cons (iterate_TLater_oLater i T1).
  Qed.

  Lemma Sub_Mu_A {Γ} T i: Γ ⊨ TMu (shift T), i <: T, i.
  Proof.
    rewrite /istpi.
    cbn [pinterp pty_interpO].
    rewrite (pty_interp_subst T (ren (+1))).
    apply sSub_Mu_A.
    (* iIntros "!>" (vs v) "**".
    by rewrite /= (lift_olty_eq (pty_interp_subst _ _)). *)
  Qed.

  Lemma Sub_Mu_B {Γ} T i: Γ ⊨ T, i <: TMu (shift T), i.
  Proof.
    rewrite /istpi.
    cbn [pinterp pty_interpO].
    rewrite (pty_interp_subst T (ren (+1))).
    apply sSub_Mu_B.
    (* iIntros "!>" (vs v) "**".
    by rewrite /= (lift_olty_eq (pty_interp_subst _ _)). *)
  Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂
     ----------------------------------------------- (<:-Bind-1)
     Γ ⊨ μ (x: T₁ˣ) <: T₂
  *)
  (* Sort-of-show this rule is derivable from Sub_Mu_X and Sub_Mu_A. *)
  Lemma Sub_Mu_1 {Γ T1 T2 i j} :
    iterate TLater i T1 :: Γ ⊨ T1, i <: shift T2, j -∗
    Γ ⊨ TMu T1, i <: T2, j.
  Proof.
    iIntros "Hstp"; iApply (Sub_Trans with "[-] []").
    by iApply Sub_Mu_X. iApply Sub_Mu_A.
  Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ <: T₂ᶻ
     ----------------------------------------------- (<:-Bind-2)
     Γ ⊨ T₁ <: μ(x: T₂ˣ)
  *)
  Lemma Sub_Mu_2 {Γ T1 T2 i j} :
    iterate TLater i (shift T1) :: Γ ⊨ (shift T1), i <: T2, j -∗
    Γ ⊨ T1, i <: TMu T2, j.
  Proof.
    iIntros "Hstp"; iApply (Sub_Trans with "[] [-]").
    iApply Sub_Mu_B. by iApply Sub_Mu_X.
  Qed.

  Lemma T_Mu_I {Γ} T v: Γ ⊨ tv v : T.|[v/] -∗ Γ ⊨ tv v : TMu T.
  Proof. by rewrite /ietp -sT_Mu_I pty_interp_subst. Qed.

  Lemma T_Mu_E {Γ} T v: Γ ⊨ tv v : TMu T -∗ Γ ⊨ tv v : T.|[v/].
  Proof. by rewrite /ietp sT_Mu_E pty_interp_subst. Qed.

  Lemma sT_All_Ex {Γ e1 v2 T1 T2}:
    Γ s⊨ e1: oAll T1 T2 -∗
    Γ s⊨ tv v2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ s⊨ tapp e1 (tv v2) : T2.|[v2/].
  Proof.
    iIntros "/= #He1 #Hv2Arg !> * #HG !>".
    smart_wp_bind (AppLCtx (tv v2.[_])) v "#Hr {He1}" ("He1" with "[#//]").
    iDestruct "Hr" as (t ->) "#HvFun".
    rewrite -wp_pure_step_later; last done.
    iSpecialize ("HvFun" with "[#]"). {
      rewrite -wp_value_inv'. by iApply ("Hv2Arg" with "[]").
    }
    iNext. iApply wp_wand.
    - iApply "HvFun".
    - iIntros (v) "{HG HvFun Hv2Arg} H".
      rewrite /= (hoEnvD_subst_one T2 v2 v) //.
  Qed.

  Lemma T_All_Ex {Γ e1 v2 T1 T2}:
    Γ ⊨ e1: TAll T1 T2 -∗ Γ ⊨ tv v2 : T1 -∗ Γ ⊨ tapp e1 (tv v2) : T2.|[v2/].
  Proof. by rewrite /ietp (pty_interp_subst T2 (v2 .: ids)) -sT_All_Ex. Qed.

  Lemma sT_All_E {Γ e1 e2 T1 T2}:
    Γ s⊨ e1 : oAll T1 (shift T2) -∗
    Γ s⊨ e2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ s⊨ tapp e1 e2 : T2.
  Proof.
    iIntros "/= #He1 #Hv2 !>" (vs) "#HG !>".
    smart_wp_bind (AppLCtx (e2.|[_])) v "#Hr" ("He1" with "[]").
    smart_wp_bind (AppRCtx v) w "#Hw" ("Hv2" with "[]").
    iDestruct "Hr" as (t ->) "#Hv".
    rewrite -wp_pure_step_later // -wp_mono /=; first by iSpecialize ("Hv" with "Hw"); iNext.
    iIntros (v); by rewrite /= (hoEnvD_weaken_one T2 _ _ _).
  Qed.

  Lemma T_All_E {Γ e1 e2 T1 T2} :
    Γ ⊨ e1 : TAll T1 (shift T2) -∗ Γ ⊨ e2 : T1 -∗ Γ ⊨ tapp e1 e2 : T2.
  Proof. by rewrite /ietp -sT_All_E -(pty_interp_subst T2 (ren (+1))). Qed.

  Lemma sSub_TVMem_Variant' {Γ T1 T2 i j l}:
    Γ s⊨ T1, i <: T2, j + i -∗
    Γ s⊨ oVMem l T1, i <: oVMem l T2, j + i.
  Proof.
    iIntros "#Hsub /= !>" (ρ v) "#Hg #HT1". setoid_rewrite laterN_plus.
    iDestruct "HT1" as (d) "#[Hdl #HT1]".
    iExists d; repeat iSplit => //.
    iDestruct "HT1" as (pmem) "[Heq HvT1]".
    iExists pmem; repeat iSplit => //; rewrite !path_wp_eq.
    iDestruct "HvT1" as (w) "[Hv HvT1]"; iExists w; iFrame "Hv".
    by iApply "Hsub".
  Qed.

  Lemma Sub_TVMem_Variant' {Γ T1 T2 i j l}:
    Γ ⊨ T1, i <: T2, j + i -∗ Γ ⊨ TVMem l T1, i <: TVMem l T2, j + i.
  Proof. apply sSub_TVMem_Variant'. Qed.

  Lemma Sub_TVMem_Variant {Γ T1 T2 i l}:
    Γ ⊨ T1, i <: T2, i -∗ Γ ⊨ TVMem l T1, i <: TVMem l T2, i.
  Proof. iApply (Sub_TVMem_Variant' (j := 0)). Qed.

  (* Stronger variant of [sT_Obj_E]. *)
  Lemma sT_Obj_E' {Γ e T l}:
    Γ s⊨ e : oVMem l (oLater T) -∗
    (*─────────────────────────*)
    Γ s⊨ tproj e l : T.
  Proof.
    iIntros "#HE /= !>" (ρ) "#HG !>".
    smart_wp_bind (ProjCtx l) v "#Hv {HE}" ("HE" with "[]").
    iDestruct "Hv" as (? Hl pmem ->) "Hv".
    rewrite -wp_pure_step_later //= path_wp_later_swap path_wp_to_wp. by [].
  Qed.

  Lemma sT_Obj_E {Γ e T l}:
    Γ s⊨ e : oVMem l T -∗
    (*─────────────────────────*)
    Γ s⊨ tproj e l : T.
  Proof.
    rewrite -sT_Obj_E'. iIntros "HE"; iApply (sT_Sub (i := 0) with "HE").
    rewrite -(sSub_TVMem_Variant' (j := 0)).
    (* iApply Sub_Add_Later. *)
    by iIntros "!> ** !> /=".
  Qed.

  Lemma T_Obj_E {Γ e T l}: Γ ⊨ e : TVMem l T -∗ Γ ⊨ tproj e l : T.
  Proof. apply sT_Obj_E. Qed.
End Sec.

Section swap_based_typing_lemmas.
  Context `{!dlangG Σ} `{!SwapPropI Σ}.

  Lemma sSub_TAllConCov {Γ T1 T2 U1 U2 i}:
    Γ s⊨ oLater T2, i <: oLater T1, i -∗
    iterate oLater (S i) (shift T2) :: Γ s⊨ oLater U1, i <: oLater U2, i -∗
    Γ s⊨ oAll T1 U1, i <: oAll T2 U2, i.
  Proof.
    rewrite iterate_S /=.
    iIntros "#HsubT #HsubU /= !>" (ρ v) "#Hg #HT1".
    iDestruct "HT1" as (t) "#[Heq #HT1]". iExists t; iSplit => //.
    iIntros (w).
    rewrite -!mlaterN_pers -mlaterN_impl.
    iIntros "!> #HwT2".
    iSpecialize ("HsubT" $! ρ w with "Hg HwT2").
    iSpecialize ("HsubU" $! (w .: ρ)); iEval (rewrite -forall_swap_impl) in "HsubU".
    iSpecialize ("HsubU" with "[# $Hg]").
    by rewrite iterate_oLater_later -swap_later /=; iApply hoEnvD_weaken_one.
    setoid_rewrite mlaterN_impl; setoid_rewrite mlater_impl.
    iNext i; iNext 1. iModIntro. iApply wp_wand.
    - iApply ("HT1" with "[]"). iApply "HsubT".
    - iIntros (u) "#HuU1". by iApply "HsubU".
  Qed.

  Lemma Sub_TAllConCov {Γ} T1 T2 U1 U2 i:
    Γ ⊨ TLater T2, i <: TLater T1, i -∗
    iterate TLater (S i) (shift T2) :: Γ ⊨ TLater U1, i <: TLater U2, i -∗
    Γ ⊨ TAll T1 U1, i <: TAll T2 U2, i.
  Proof.
    rewrite /istpi fmap_cons iterate_TLater_oLater.
    rewrite (pty_interp_subst T2 (ren (+1))).
    apply sSub_TAllConCov.
  Qed.

  Lemma sSub_TTMem_Variant' {Γ L1 L2 U1 U2 i j l}:
    Γ s⊨ oLater L2, j + i <: oLater L1, i -∗
    Γ s⊨ oLater U1, i <: oLater U2, i -∗
    Γ s⊨ oTMem l L1 U1, i <: oTMem l L2 U2, i.
  Proof.
    iIntros "#IHT #IHT1 /= !>" (ρ v) "#Hg #HT1".
    iDestruct "HT1" as (d) "[Hl2 H]".
    iDestruct "H" as (φ) "#[Hφl [HLφ #HφU]]".
    rewrite (comm plus).
    setoid_rewrite laterN_plus; setoid_rewrite mlaterN_impl.
    iExists d; repeat iSplit; first by iNext.
    iExists φ; repeat iSplitL; first by [iNext];
      rewrite -!mlaterN_pers;
      iIntros "!>" (w);
      iSpecialize ("IHT" $! ρ w with "Hg");
      iSpecialize ("IHT1" $! ρ w with "Hg");
      iNext i; iIntros.
    - iApply "HLφ" => //. by iApply "IHT".
    - iApply "IHT1". by iApply "HφU".
  Qed.

  Lemma sSub_TTMem_Variant {Γ L1 L2 U1 U2 i l}:
    Γ s⊨ oLater L2, i <: oLater L1, i -∗
    Γ s⊨ oLater U1, i <: oLater U2, i -∗
    Γ s⊨ oTMem l L1 U1, i <: oTMem l L2 U2, i.
  Proof. apply (sSub_TTMem_Variant' (j := 0)). Qed.

  Lemma Sub_TTMem_Variant {Γ L1 L2 U1 U2 i l}:
    Γ ⊨ TLater L2, i <: TLater L1, i -∗
    Γ ⊨ TLater U1, i <: TLater U2, i -∗
    Γ ⊨ TTMem l L1 U1, i <: TTMem l L2 U2, i.
  Proof. apply sSub_TTMem_Variant. Qed.
End swap_based_typing_lemmas.
