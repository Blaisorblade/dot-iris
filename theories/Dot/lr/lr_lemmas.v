From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

From D Require Import swap_later_impl.
From D.Dot Require Import rules synLemmas unary_lr.

Reserved Notation "⊢G Γ1 <:* Γ2" (at level 74, Γ1, Γ2 at next level).
Reserved Notation "⊢T T1 <: T2" (at level 74, T1, T2 at next level).

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx) (ρ : env).

(** * When is a context weaker than another? *)
(* Likely, this should be an iProp. *)
Definition ty_sub `{HdlangG: dlangG Σ} T1 T2 := ∀ ρ v, ⟦ T1 ⟧ ρ v -∗ ⟦ T2 ⟧ ρ v.
Notation "⊨T T1 <: T2" := (ty_sub T1 T2) (at level 74, T1, T2 at next level).
Typeclasses Opaque ty_sub.

Definition ctx_sub `{HdlangG: dlangG Σ} Γ1 Γ2 : Prop := ∀ ρ, ⟦ Γ1 ⟧* ρ -∗ ⟦ Γ2 ⟧* ρ.
Notation "⊨G Γ1 <:* Γ2" := (ctx_sub Γ1 Γ2) (at level 74, Γ1, Γ2 at next level).
Typeclasses Opaque ctx_sub.

(** Create an [f_equiv] database, inspired by stdpp's [f_equal] database. We
don't restrict it to [(_ ≡ _)], because [f_equiv] can apply [Proper]
instances to any relation. *)
Hint Extern 998 => f_equiv : f_equiv.

(* Global Instance: Params (@ietp) 2. *)

(** A left inverse of TLater. Sometimes written ⊲. *)
Definition unTLater T : ty := match T with | TLater T' => T' | _ => T end.

Definition unTLater_TLater T: unTLater (TLater T) = T := reflexivity _.
Global Instance: Cancel (=) unTLater TLater. Proof. exact: unTLater_TLater. Qed.

Inductive ty_sub_syn : ty → ty → Prop :=
| ty_id_sub_syn T : ⊢T T <: T
| ty_trans_sub_syn T1 T2 T3 : ⊢T T1 <: T2 → ⊢T T2 <: T3 → ⊢T T1 <: T3
| unTLater_ty_sub_syn T : ⊢T unTLater T <: T
| ty_sub_TLater_syn T : ⊢T T <: TLater T
where "⊢T T1 <: T2" := (ty_sub_syn T1 T2).
Hint Constructors ty_sub_syn : ctx_sub.

Inductive ctx_sub_syn : ctx → ctx → Prop :=
| ctx_id_syn Γ : ⊢G Γ <:* Γ
| ctx_trans_sub_syn Γ1 Γ2 Γ3 :
  ⊢G Γ1 <:* Γ2 → ⊢G Γ2 <:* Γ3 → ⊢G Γ1 <:* Γ3
| unTLater_ctx_sub_syn Γ :
  ⊢G unTLater <$> Γ <:* Γ
| ctx_sub_TLater_syn Γ :
  ⊢G Γ <:* TLater <$> Γ
| ctx_sub_TLater_unTLater_syn Γ :
  ⊢G Γ <:* TLater <$> (unTLater <$> Γ)
| TLater_cong_ctx_sub_syn Γ1 Γ2 :
  ⊢G Γ1 <:* Γ2 →
  ⊢G TLater <$> Γ1 <:* TLater <$> Γ2
| ctx_sub_cons_syn T1 T2 Γ1 Γ2 :
  ⊢T T1 <: T2 →
  ⊢G Γ1 <:* Γ2 →
  ⊢G T1 :: Γ1 <:* T2 :: Γ2
where "⊢G Γ1 <:* Γ2" := (ctx_sub_syn Γ1 Γ2).
Hint Constructors ctx_sub_syn : ctx_sub.


Section CtxSub.
  Context `{HdlangG: dlangG Σ}.

  (** * Basic lemmas about [ctx_sub]. *)
  (* TODO: Make this into a structural typing rule? *)
  Global Instance: RewriteRelation ty_sub := {}.
  Global Instance: PreOrder ty_sub.
  Proof. split. by move => ??. by move => x y z H1 H2 ρ v; rewrite (H1 _ _). Qed.
  (* Proof. split. by iIntros (???) "$". iIntros (x y z H1 H2 ρ v). iRewrite (H1 _ _). Qed. *)

  Global Instance: RewriteRelation ctx_sub := {}.
  Global Instance: PreOrder ctx_sub.
  Proof. split. by move => ??. by move => x y z H1 H2 ρ; rewrite (H1 _). Qed.

  Global Instance Proper_cons_ctx_sub : Proper (ty_sub ==> ctx_sub ==> ctx_sub) cons.
  Proof. move => T1 T2 HlT Γ1 Γ2 Hl ρ /=. by rewrite (HlT _) (Hl _). Qed.

  Global Instance Proper_cons_ctx_sub_flip : Proper (flip ty_sub ==> flip ctx_sub ==> flip ctx_sub) cons.
  Proof. solve_proper. Qed.

  (** Typing is contravariant in [Γ]. *)
  Global Instance Proper_ietp : Proper (flip ctx_sub ==> (=) ==> (=) ==> (⊢)) ietp.
  Proof. move => /= Γ1 Γ2 Hweak ??????; subst. by setoid_rewrite (Hweak _). Qed.
  Global Instance Proper_ietp_flip : Proper (ctx_sub ==> (=) ==> (=) ==> flip (⊢)) ietp.
  Proof. move => /= Γ1 Γ2 Hweak ??????; subst. by setoid_rewrite (Hweak _). Qed.

  Global Instance : Proper (ty_sub ==> ty_sub) TLater.
  Proof. intros x y Hl ??. by rewrite /= (Hl _ _). Qed.
  Global Instance : Proper (flip ty_sub ==> flip ty_sub) TLater.
  Proof. solve_proper. Qed.

  Lemma env_TLater_commute Γ ρ : ⟦ TLater <$> Γ ⟧* ρ ⊣⊢ ▷ ⟦ Γ ⟧* ρ.
  Proof.
    elim: Γ ρ => [| T Γ IH] ρ; cbn; [|rewrite IH later_and];
      iSplit; by [iIntros "$" | iIntros "_"].
  Qed.

  Global Instance : Proper (ctx_sub ==> ctx_sub) (fmap TLater).
  Proof. intros xs ys Hl ?. by rewrite !env_TLater_commute (Hl _). Qed.
  Global Instance : Proper (flip ctx_sub ==> flip ctx_sub) (fmap TLater).
  Proof. solve_proper. Qed.

  (** The strength ordering of contexts lifts the strength ordering of types. *)
  Lemma env_lift_sub f g {Γ} (Hle: ∀ T, ⊨T f T <: g T):
    ⊨G f <$> Γ <:* g <$> Γ.
  Proof. elim: Γ => [//| T Γ IH] ρ; cbn. by rewrite (Hle T _ _) -(IH _). Qed.

  Lemma env_lift_sub' f g Γ {Γ1 Γ2}:
    Γ1 = f <$> Γ → Γ2 = g <$> Γ →
    (∀ T, ⊨T f T <: g T) →
    ⊨G Γ1 <:* Γ2.
  Proof. move => -> -> Hweak. exact: env_lift_sub. Qed.

  (** Ordering of logical strength:
      unTLater T <: T <: TLater (unTLater T) <: TLater T. *)

  Lemma unTLater_ty_sub T : ⊨T unTLater T <: T.
  Proof. case: T => //= T ??; by auto. Qed.

  Lemma ty_sub_TLater_unTLater T : ⊨T T <: TLater (unTLater T).
  Proof. destruct T => ??; iIntros "$". Qed.

  Lemma ty_sub_TLater T : ⊨T T <: TLater T.
  Proof. by intros ?; auto. Qed.

  Hint Resolve ty_sub_TLater ty_sub_TLater_unTLater unTLater_ty_sub : ctx_sub.

  (* Unused *)
  Lemma TLater_unTLater_ty_sub_TLater T :
    ⊨T TLater (unTLater T) <: TLater T.
  Proof. by rewrite unTLater_ty_sub. Qed.

  Lemma fundamental_ty_sub {T1 T2} : ⊢T T1 <: T2 → ⊨T T1 <: T2.
  Proof. induction 1; auto with ctx_sub; by [|etrans]. Qed.
  Hint Resolve fundamental_ty_sub : ctx_sub.

  (** Lift the above ordering to environments. *)
  Lemma unTLater_ctx_sub Γ : ⊨G unTLater <$> Γ <:* Γ.
  Proof. eapply env_lift_sub', unTLater_ty_sub; by rewrite ?list_fmap_id. Qed.

  Lemma ctx_sub_TLater Γ : ⊨G Γ <:* TLater <$> Γ.
  Proof. eapply env_lift_sub', ty_sub_TLater; by rewrite ?list_fmap_id. Qed.

  Lemma ctx_sub_TLater_unTLater Γ : ⊨G Γ <:* TLater <$> (unTLater <$> Γ).
  Proof.
    rewrite -list_fmap_compose.
    eapply env_lift_sub', ty_sub_TLater_unTLater; by rewrite ?list_fmap_id.
  Qed.

  Hint Resolve ctx_sub_TLater ctx_sub_TLater_unTLater unTLater_ctx_sub : ctx_sub.

  Lemma fundamental_ctx_sub {Γ1 Γ2} : ⊢G Γ1 <:* Γ2 → ⊨G Γ1 <:* Γ2.
  Proof. induction 1; auto with f_equiv ctx_sub; by [|etrans]. Qed.

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

  Lemma T_Forall_I_Strong {Γ} T1 T2 e:
    shift T1 :: (unTLater <$> Γ) ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "#HeT !>" (ρ) "#HG /= !>".
    rewrite -wp_value'. iExists _; iSplit; first done.
    iIntros "!>" (v) "#Hv"; rewrite up_sub_compose.
    (* Factor ⪭ out of [⟦ Γ ⟧* ρ] before [iNext]. *)
    rewrite (ctx_sub_TLater_unTLater _ _) env_TLater_commute.
    iNext.
    iApply ("HeT" $! (v .: ρ) with "[$HG]").
    by rewrite (interp_weaken_one T1 _ v) stail_eq.
  Qed.

  (* Derivable *)
  Lemma T_Forall_I {Γ} T1 T2 e:
    shift T1 :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  (* Proof. by rewrite -T_Forall_I_Strong (unTLater_ctx_sub Γ). Qed. *)
  Proof. rewrite -T_Forall_I_Strong. ietp_weaken_ctx. Qed.

  Lemma P_Val {Γ} v T:
    Γ ⊨ tv v : T -∗
    Γ ⊨p pv v : T, 0.
  Proof.
    iIntros "/= #Hp !>" (ρ) "Hg".
    iSpecialize ("Hp" with "Hg"); rewrite wp_value_inv'.
    by rewrite path_wp_pv.
  Qed.

  (** Lemmas about definition typing. *)
  Lemma D_Path_TVMem_I {Γ} T p l:
    Γ ⊨p p : T, 0 -∗
    Γ ⊨ { l := dpt p } : TVMem l T.
  Proof.
    iIntros "/= #Hv !>" (ρ Hpid) "#Hg".
    rewrite def_interp_tvmem_eq.
    iApply ("Hv" with "Hg").
  Qed.

  (** Lemmas about definition typing. *)
  Lemma D_TVMem_I {Γ} T v l:
    Γ ⊨ tv v : T -∗
    Γ ⊨ { l := dpt (pv v) } : TVMem l T.
  Proof. by rewrite -D_Path_TVMem_I -P_Val. Qed.

  (* Derivable *)
  Lemma D_TVMem_All_I_Strong {Γ} T1 T2 e l:
    shift T1 :: (unTLater <$> Γ) ⊨ e : T2 -∗
    Γ ⊨ { l := dpt (pv (vabs e)) } : TVMem l (TAll T1 T2).
  Proof. by rewrite -D_TVMem_I -T_Forall_I_Strong. Qed.

  Lemma D_TVMem_All_I {Γ} V T1 T2 e l:
    shift T1 :: V :: Γ ⊨ e : T2 -∗
    Γ |L V ⊨ { l := dpt (pv (vabs e)) } : TVMem l (TAll T1 T2).
  Proof.
    (* Compared to [T_Forall_I], we must strip later also from [TLater V]. *)
    rewrite -D_TVMem_All_I_Strong fmap_cons cancel.
    ietp_weaken_ctx.
  Qed.
End LambdaIntros.

Section Sec.
  Context `{HdlangG: dlangG Σ} Γ.

  Lemma T_Sub e T1 T2 i:
    Γ ⊨ e : T1 -∗
    Γ ⊨ T1, 0 <: T2, i -∗
    (*───────────────────────────────*)
    Γ ⊨ iterate tskip i e : T2.
  Proof.
    iIntros "/= #HeT1 #Hsub !>" (ρ) "#Hg !>".
    rewrite tskip_subst -wp_bind.
    iApply (wp_wand with "(HeT1 Hg)").
    iIntros (v) "#HvT1".
    (* We can swap ▷^i with WP (tv v)! *)
    rewrite -wp_pure_step_later // -wp_value.
    by iApply "Hsub".
  Qed.

  Lemma T_Var x T:
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ ⊨ tv (ids x) : shiftN x T.
  Proof.
    iIntros (Hx) "/= !> * #Hg".
    rewrite -wp_value' interp_env_lookup; by [].
  Qed.

  (*
     x ∉ fv T
     ----------------------------------------------- (<:)
     Γ ⊨ mu x: T <: T    Γ ⊨ T <: mu(x: T)
  *)

  Lemma interp_TMu_ren T ρ v: ⟦ TMu (shift T) ⟧ ρ v ≡ ⟦ T ⟧ ρ v.
  Proof. by rewrite /= (interp_weaken_one T (_ .: ρ) v). Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂ᶻ
     ----------------------------------------------- (<:-μ-X)
     Γ ⊨ μ (x: T₁ˣ) <: μ(x: T₂ˣ)
  *)
  (* Notation "◁ n T ▷" := (iterate TLater n T). *)
  Lemma Sub_Mu_X T1 T2 i j:
    iterate TLater i T1 :: Γ ⊨ T1, i <: T2, j -∗
    Γ ⊨ TMu T1, i <: TMu T2, j.
  Proof.
    iIntros "/= #Hstp !>" (vs v) "#Hg #HT1".
    iApply ("Hstp" $! (v .: vs) v with "[# $Hg] [#//]").
    by rewrite iterate_TLater_later.
  Qed.

  (* Novel subtyping rules. Sub_Mu_1 and Sub_Mu_2 become (sort-of?)
  derivable. *)
  Lemma Sub_Mu_A T i: Γ ⊨ TMu (shift T), i <: T, i.
  Proof. iIntros "!>" (vs v) "**". by rewrite (interp_TMu_ren T vs v). Qed.

  Lemma Sub_Mu_B T i: Γ ⊨ T, i <: TMu (shift T), i.
  Proof. iIntros "!>" (vs v) "**". by rewrite (interp_TMu_ren T vs v). Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂
     ----------------------------------------------- (<:-Mu-1)
     Γ ⊨ μ (x: T₁ˣ) <: T₂
  *)
  (* Sort-of-show this rule is derivable from Sub_Mu_X and Sub_Mu_A. *)
  Lemma Sub_Mu_1 T1 T2 i j:
    iterate TLater i T1 :: Γ ⊨ T1, i <: shift T2, j -∗
    Γ ⊨ TMu T1, i <: T2, j.
  Proof. iIntros "Hstp"; iApply (Sub_Trans with "[-] []"). by iApply Sub_Mu_X. iApply Sub_Mu_A. Qed.
  (*
     Γ, z: T₁ᶻ ⊨ T₁ <: T₂ᶻ
     ----------------------------------------------- (<:-Bind-2)
     Γ ⊨ T₁ <: μ(x: T₂ˣ)
  *)

  Lemma Sub_Mu_2 T1 T2 i j:
    iterate TLater i (shift T1) :: Γ ⊨ (shift T1), i <: T2, j -∗
    Γ ⊨ T1, i <: TMu T2, j.
  Proof. iIntros "Hstp"; iApply (Sub_Trans with "[] [-]"). iApply Sub_Mu_B. by iApply Sub_Mu_X. Qed.

  (*
     Γ ⊨ z: Tᶻ
     =============================================== (T-Rec-I/T-Rec-E)
     Γ ⊨ z: mu(x: Tˣ)
   *)
  Lemma TMu_equiv T v: (Γ ⊨ tv v : TMu T) ≡ (Γ ⊨ tv v : T.|[v/]).
  Proof.
    iSplit; iIntros "/= #Htp !>" (vs) "#Hg !>";
    iDestruct (wp_value_inv with "(Htp Hg)") as "{Htp} Hgoal";
    rewrite -wp_value (interp_subst_one T v (v.[vs])); done.
  Qed.

  Lemma TMu_I T v: Γ ⊨ tv v : T.|[v/] -∗ Γ ⊨ tv v : TMu T.
  Proof. by rewrite TMu_equiv. Qed.

  Lemma TMu_E T v: Γ ⊨ tv v : TMu T -∗ Γ ⊨ tv v : T.|[v/].
  Proof. by rewrite TMu_equiv. Qed.

  Lemma T_Forall_E e1 e2 T1 T2:
    Γ ⊨ e1 : TAll T1 (shift T2) -∗
    Γ ⊨ e2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ ⊨ tapp e1 e2 : T2.
  Proof.
    iIntros "/= #He1 #Hv2 !>" (vs) "#HG !>".
    smart_wp_bind (AppLCtx (e2.|[_])) v "#Hr" ("He1" with "[]").
    smart_wp_bind (AppRCtx v) w "#Hw" ("Hv2" with "[]").
    iDestruct "Hr" as (t ->) "#Hv".
    rewrite -wp_pure_step_later // -wp_mono /=; first by iSpecialize ("Hv" with "Hw"); iNext.
    iIntros (v); by rewrite (interp_weaken_one T2 _ v).
  Qed.

  Lemma T_Forall_Ex e1 v2 T1 T2:
    Γ ⊨ e1: TAll T1 T2 -∗
    Γ ⊨ tv v2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ ⊨ tapp e1 (tv v2) : T2.|[v2/].
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
      rewrite (interp_subst_one T2 v2 v) //.
  Qed.


  Lemma Sub_TVMem_Variant' T1 T2 i j l:
    Γ ⊨ T1, i <: T2, j + i -∗
    Γ ⊨ TVMem l T1, i <: TVMem l T2, j + i.
  Proof.
    iIntros "#Hsub /= !>" (ρ v) "#Hg #HT1". setoid_rewrite laterN_plus.
    iDestruct "HT1" as (d) "#[Hdl #HT1]".
    iExists d; repeat iSplit => //.
    iDestruct "HT1" as (pmem) "[Heq HvT1]".
    iExists pmem; repeat iSplit => //; rewrite !path_wp_eq.
    iDestruct "HvT1" as (w) "[Hv HvT1]"; iExists w; iFrame "Hv".
    by iApply "Hsub".
  Qed.

  Lemma Sub_TVMem_Variant T1 T2 i l:
    Γ ⊨ T1, i <: T2, i -∗
    Γ ⊨ TVMem l T1, i <: TVMem l T2, i.
  Proof. iApply (Sub_TVMem_Variant' _ _ _ 0). Qed.

  (* Stronger variant of T_Mem_E. *)
  Lemma T_Mem_E' e T l:
    Γ ⊨ e : TVMem l (TLater T) -∗
    (*─────────────────────────*)
    Γ ⊨ tproj e l : T.
  Proof.
    iIntros "#HE /= !>" (ρ) "#HG !>".
    smart_wp_bind (ProjCtx l) v "#Hv {HE}" ("HE" with "[]").
    iDestruct "Hv" as (? Hl pmem ->) "Hv".
    rewrite -wp_pure_step_later //= path_wp_later_swap path_wp_to_wp. by [].
  Qed.

  Lemma T_Mem_E e T l:
    Γ ⊨ e : TVMem l T -∗
    (*─────────────────────────*)
    Γ ⊨ tproj e l : T.
  Proof.
    rewrite -T_Mem_E'. iIntros "HE"; iApply (T_Sub e _ _ 0 with "HE").
    rewrite -Sub_TVMem_Variant.
    (* iApply Sub_Add_Later. *)
    by iIntros "!> ** !> /=".
  Qed.

End Sec.

Section swap_based_typing_lemmas.
  Context `{!dlangG Σ} {Γ} `{!SwapPropI Σ}.

  Lemma Sub_TAllConCov T1 T2 U1 U2 i:
    Γ ⊨ TLater T2, i <: TLater T1, i -∗
    iterate TLater (S i) (shift T2) :: Γ ⊨ TLater U1, i <: TLater U2, i -∗
    Γ ⊨ TAll T1 U1, i <: TAll T2 U2, i.
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
    by rewrite iterate_TLater_later -swap_later; iApply interp_weaken_one.
    setoid_rewrite mlaterN_impl; setoid_rewrite mlater_impl.
    iNext i; iNext 1. iModIntro. iApply wp_wand.
    - iApply ("HT1" with "[]"). iApply "HsubT".
    - iIntros (u) "#HuU1". by iApply "HsubU".
  Qed.

  Lemma Sub_TTMem_Variant' L1 L2 U1 U2 i j l:
    Γ ⊨ TLater L2, j + i <: TLater L1, i -∗
    Γ ⊨ TLater U1, i <: TLater U2, i -∗
    Γ ⊨ TTMem l L1 U1, i <: TTMem l L2 U2, i.
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

  Lemma Sub_TTMem_Variant L1 L2 U1 U2 i l:
    Γ ⊨ TLater L2, i <: TLater L1, i -∗
    Γ ⊨ TLater U1, i <: TLater U2, i -∗
    Γ ⊨ TTMem l L1 U1, i <: TTMem l L2 U2, i.
  Proof. apply Sub_TTMem_Variant' with (j := 0). Qed.
End swap_based_typing_lemmas.
