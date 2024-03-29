From D Require Import tactics.
From D.Dot Require Import syn ex_utils old_unstamped_typing.
From D.Dot Require Import unstampedness_binding.
From D.Dot Require Import path_repl_lemmas
  old_subtyping_derived_rules.
Import DBNotation.
Export old_subtyping_derived_rules.

Lemma is_unstamped_pvar i n b : i < n → is_unstamped_path n b (pv (vvar i)).
Proof. eauto 7. Qed.
#[global] Hint Resolve is_unstamped_pvar : core.
Lemma is_unstamped_pvars i n l b : i < n → is_unstamped_ty n b (pv (vvar i) @; l).
Proof. eauto. Qed.
#[global] Hint Resolve is_unstamped_pvars : core.

Lemma iT_Mu_E {Γ x T} :
  Γ u⊢ₜ tv (vvar x) : TMu T →
  is_unstamped_ty' (length Γ).+1 T →
  Γ u⊢ₜ tv (vvar x) : T.|[vvar x/].
Proof. move => Hx Hu. by eapply iT_Path', iP_Mu_E', iP_VarT, Hx. Qed.

Lemma iT_Mu_I {Γ x T} :
  Γ u⊢ₜ tv (vvar x) : T.|[vvar x/] →
  (*──────────────────────*)
  is_unstamped_ty' (length Γ).+1 T →
  Γ u⊢ₜ tv (vvar x) : TMu T.
Proof. move => Hx Hu. by eapply iT_Path', iP_Mu_I', iP_VarT, Hx. Qed.

Ltac tcrush :=
  repeat first [ eassumption | reflexivity |
  apply iT_Mu_I | apply iT_Mu_E |
  typconstructor | stcrush ].

Lemma iT_All_Ex Γ e1 x2 T1 T2 :
  Γ u⊢ₜ e1 : TAll T1 T2 →
  Γ u⊢ₜ tv (vvar x2) : T1 →
  is_unstamped_ty' (length Γ).+1 T2 →
  (*────────────────────────────────────────────────────────────*)
  Γ u⊢ₜ tapp e1 (tv (vvar x2)) : T2.|[vvar x2/].
Proof.
  intros He1 Hx2 Hu.
  rewrite -(psubst_subst_agree_ty (n := S (length Γ))); tcrush.
  eapply iT_All_E_p with (p2 := pv (vvar x2)); tcrush.
Qed.

Ltac wtcrush := repeat first [ fast_done | typconstructor | stcrush ] ; try solve [
  first [
    by eauto 3 using is_unstamped_TLater_n, is_unstamped_ren1_ty, is_unstamped_ren1_path |
    try_once is_unstamped_weaken_ty ]; eauto].

Ltac ltcrush := tcrush; repeat lookup.

Ltac hideCtx :=
  let hideCtx' Γ := (let x := fresh "Γ" in set x := Γ) in
  match goal with
  | |- ?Γ u⊢ₜ _ : _ => hideCtx' Γ
  | |- ?Γ u⊢ₜ _, _ <: _, _ => hideCtx' Γ
  | |- ?Γ u⊢ₚ _ : _, _  => hideCtx' Γ
  | |- ?Γ u⊢{ _ := _  } : _ => hideCtx' Γ
  | |- ?Γ u⊢ds _ : _ => hideCtx' Γ
  end.

Lemma iT_Var' Γ x T1 T2 :
  Γ !! x = Some T1 →
  T2 = shiftN x T1 →
  (*──────────────────────*)
  Γ u⊢ₜ tv (vvar x) : T2.
Proof. intros; apply iT_Path'; pvar. Qed.

Lemma iT_Var0 Γ T :
  Γ !! 0 = Some T →
  (*──────────────────────*)
  Γ u⊢ₜ tv (vvar 0) : T.
Proof. intros; apply iT_Path'; pvar. Qed.

Ltac var := exact: iT_Var0 || exact: iT_Var' || pvar.

Lemma iT_Var_Sub Γ x T1 T2 :
  Γ !! x = Some T1 →
  Γ u⊢ₜ shiftN x T1, 0 <: T2, 0 →
  (*──────────────────────*)
  Γ u⊢ₜ tv (vvar x) : T2.
Proof. by intros; apply iT_Path'; pvarsub. Qed.

Lemma iT_Var0_Sub Γ T1 T2 :
  Γ !! 0 = Some T1 →
  Γ u⊢ₜ T1, 0 <: T2, 0 →
  (*──────────────────────*)
  Γ u⊢ₜ tv (vvar 0) : T2.
Proof. by intros; apply iT_Path'; pvarsub. Qed.

Ltac varsub := (eapply iP_Var_Sub || eapply iP_Var0_Sub ||
  eapply iT_Var0_Sub || eapply iT_Var_Sub); first done.

Lemma iT_ISub_nocoerce T1 T2 {Γ e} :
  Γ u⊢ₜ e : T1 →
  Γ u⊢ₜ T1, 0 <: T2, 0 →
  Γ u⊢ₜ e : T2.
Proof. intros. exact: (iT_ISub (i:=0)). Qed.
#[global] Hint Resolve iT_ISub_nocoerce : core.

Lemma iT_All_Ex' T2 {Γ e1 x2 T1 T3} :
  Γ u⊢ₜ e1 : TAll T1 T2 →                        Γ u⊢ₜ tv (ids x2) : T1 →
  T3 = T2.|[ids x2/] →
  is_unstamped_ty' (length Γ).+1 T2 →
  (*────────────────────────────────────────────────────────────*)
  Γ u⊢ₜ tapp e1 (tv (ids x2)) : T3.
Proof. intros; subst; exact: iT_All_Ex. Qed.

Lemma iT_Mu_E' {Γ x T1 T2} :
  Γ u⊢ₜ tv (ids x) : μ T1 →
  T2 = T1.|[ids x/] →
  is_unstamped_ty' (length Γ).+1 T1 →
  (*──────────────────────*)
  Γ u⊢ₜ tv (ids x) : T2.
Proof. intros; subst; tcrush. Qed.

(** * Derived constructions. *)
Lemma val_LB L U Γ i x l :
  Γ u⊢ₜ tv (ids x) : type l >: L <: U →
  Γ u⊢ₜ ▶: L, i <: pv (ids x) @; l, i.
Proof.
  intros Hv; apply (iSub_SelL (p := pv _) (U := U)).
  apply (path_tp_delay (i := 0)); wtcrush.
Qed.

Lemma val_UB L U Γ i x l :
  Γ u⊢ₜ tv (ids x) : type l >: L <: U →
  Γ u⊢ₜ pv (ids x) @; l, i <: ▶: U, i.
Proof.
  intros Hv; apply (iSel_SubL (p := pv _) (L := L)).
  apply (path_tp_delay (i := 0)); wtcrush.
Qed.

Lemma iT_Let Γ t u T U :
  Γ u⊢ₜ t : T →
  shift T :: Γ u⊢ₜ u : shift U →
  Γ u⊢ₜ lett t u : U.
Proof. move => Ht Hu. apply /iT_All_E /Ht /iT_All_I /Hu. Qed.

Lemma iD_Typ Γ T l :
  is_unstamped_ty' (length Γ) T →
  Γ u⊢{ l := dtysyn T } : TTMemL l T T.
Proof. intros. tcrush. Qed.

Lemma iD_Path_Sngl {Γ} p l T :
  Γ u⊢ₚ p : T, 0 →
  Γ u⊢{ l := dpt p } : TVMem l (TSing p).
Proof. intros Hp. eapply iD_Path, iP_Sngl_Refl, Hp. Qed.

Ltac mltcrush := tcrush; try ((apply iSub_Bind_1' || apply iSub_Bind_1); tcrush); repeat lookup.

(* Simplified package introduction, for talk. *)
Lemma BindSpec Γ (L T U : ty) :
  is_unstamped_ty' (length Γ).+1 T →
  {@ type "A" >: T <: T }%ty :: Γ u⊢ₜ L, 1 <: T, 1 →
  {@ type "A" >: T <: T }%ty :: Γ u⊢ₜ T, 1 <: U, 1 →
  Γ u⊢ₜ tv (ν {@ type "A" = T }) : μ {@ type "A" >: L <: U }.
Proof.
  intros.
  eapply iT_ISub_nocoerce with (T1 := μ {@ type "A" >: T <: T }); ltcrush.
Qed.

Lemma iD_Lam_Sub {Γ} V T1 T2 e l L :
  shift T1 :: V :: Γ u⊢ₜ e : T2 →
  TLater V :: Γ u⊢ₜ TAll T1 T2, 0 <: L, 0 →
  Γ |L V u⊢{ l := dpt (pv (vabs e)) } : TVMem l L.
Proof.
  intros He Hsub. apply iD_Val.
  eapply (iT_ISub (i := 0)); first apply Hsub.
  by apply iT_All_I_strip1.
Qed.

(* Note how we must weaken the type (or its environment) to account for the
   self-variable of the created object. *)
Definition packTV l T := (ν {@ type l = shift T }).

Lemma packTV_typed' T n Γ l :
  is_unstamped_ty' n T →
  n <= length Γ →
  Γ u⊢ₜ tv (packTV l T) : typeEq l T.
Proof.
  move => HsT1 Hle; move: (Hle) (HsT1) => /le_n_S Hles /is_unstamped_ren1_ty HsT2.
  apply (iT_ISub_nocoerce (μ {@ typeEq l (shift T) }));
    last (ettrans; first apply: (iMu_Sub _ {@ typeEq l T }); wtcrush).
  apply iT_Obj_I; wtcrush.
Qed.

Lemma packTV_typed T Γ l :
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₜ tv (packTV l T) : typeEq l T.
Proof. intros; exact: packTV_typed'. Qed.

Definition tyApp t l T :=
  lett t (lett (tv (packTV l (shift T))) (tapp (tv x1) (tv x0))).

Lemma tyApp_typed Γ T U V t l :
  Γ u⊢ₜ t : TAll (tparam l) U →
  (** This subtyping premise is needed to perform "avoidance", as in compilers
    for ML and Scala: that is, producing a type [V] that does not refer to
    variables bound by let in the expression. *)
  (∀ L, typeEq l (shiftN 2 T) :: L :: Γ u⊢ₜ U.|[up (ren (+1))], 0 <: shiftN 2 V, 0) →
  is_unstamped_ty' (length Γ) T →
  is_unstamped_ty' (length Γ).+1 U →
  Γ u⊢ₜ tyApp t l T : V.
Proof.
  move => Ht Hsub HuT1 HuU1.
  eapply iT_Let; [exact: Ht|wtcrush].
  eapply iT_Let; [apply packTV_typed|]; wtcrush.
  rewrite /= -!hrenS -/(typeEq _ _).

  apply /iT_ISub_nocoerce /Hsub.

  eapply iT_All_Ex'; first var.
  have HuT3 : is_unstamped_ty' (length Γ).+2 (shiftN 2 T)
    by rewrite hrenS; wtcrush.
  varsub; tcrush; rewrite !hsubst_comp; f_equal. autosubst.
  asimpl.
  eapply is_unstamped_sub_ren_ty, HuU1.
  by move => [|i] Hi //=; [constructor => /=| eauto].
Qed.

(** * Manipulating laters, more. *)
(* This can be useful when [T] is a singleton type. *)
Lemma dropLaters Γ e T U i :
  Γ u⊢ₜ e : T →
  Γ u⊢ₜ T, 0 <: iterate TLater i U, 0 →
  Γ u⊢ₜ iterate tskip i e : TAnd T U.
Proof.
  intros HeT Hsub.
  eapply iT_ISub, HeT => {HeT}.
  typconstructor; [exact: iSub_AddI|].
  ettrans; [apply: Hsub|] => {Hsub}.
  have := (iLaterN_Sub 0 i (T := U)); rewrite plusnO; exact.
Qed.

(**
  Like [let: x := e1 in e2], but dropping [i] laters from [e1]'s type while
  preserving its identity by adding a singleton type. See
*)
Definition deLater e1 i e2 := lett e1 (lett (iterate tskip i (tv x0)) e2).

Lemma deLaterSingV0 {Γ} p i e T U :
  Γ u⊢ₚ p : TSing p, 0 →
  shift (TSing p) :: Γ u⊢ₜ shift (TSing p), 0 <: iterate TLater i T, 0 →
  TAnd (TSing (shiftN 2 p)) (shift T) :: TSing (shift p) :: Γ u⊢ₜ e : shiftN 2 U →
  Γ u⊢ₜ deLater (path2tm p) i e : U.
Proof.
  intros HpT1 Hsub HeU.
  apply iT_Let with (T := TSing p); tcrush.
  apply iT_Let with (T := TAnd (shift (TSing p)) T); rewrite /= -?hrenS; wtcrush.
  apply dropLaters; [ var | .. ]; rewrite /= -?hrenS; wtcrush.
Qed.

(** More general version of [deLaterSingV0]. Not sure if too general or useful. *)
Lemma deLaterSingV1 {Γ} p i e T1 T2 U :
  Γ u⊢ₚ p : T1, 0 →
  shift (TAnd (TSing p) T1) :: Γ u⊢ₜ shift T1, 0 <: iterate TLater i T2, 0 →
  TAnd (TAnd (TSing (shiftN 2 p)) (shiftN 2 T1)) (shift T2) ::
    TAnd (TSing (shift p)) (shift T1) :: Γ u⊢ₜ e : shiftN 2 U →
  Γ u⊢ₜ deLater (path2tm p) i e : U.
Proof.
  intros HpT1 Hsub HeU.
  apply iT_Let with (T := TAnd (TSing p) T1); tcrush.
  by apply iP_And_I, HpT1; eapply iP_Sngl_Refl, HpT1.
  apply iT_Let with (T := TAnd (shift (TAnd (TSing p) T1)) T2); rewrite /= -?hrenS; wtcrush.
  apply dropLaters; [ var | lNext | ..]; rewrite /= -?hrenS; wtcrush.
Qed.

(** Best version of [deLaterSing]. *)
Lemma deLaterSing {Γ} p i e T1 U :
  Γ u⊢ₚ p : iterate TLater i T1, 0 →
  TAnd (TSing (shiftN 2 p)) (shiftN 2 T1) ::
    TAnd (TSing (shift p)) (iterate TLater i (shift T1)) :: Γ u⊢ₜ e : shiftN 2 U →
  Γ u⊢ₜ deLater (path2tm p) i e : U.
Proof.
  intros HpT1 HeU.
  apply iT_Let with (T := TAnd (TSing p) (iterate TLater i T1)); wtcrush.
  by apply iP_And_I, HpT1; eapply iP_Sngl_Refl, HpT1.
  apply iT_Let with (T := TAnd (TSing (shift p)) (shift T1));
    rewrite /= -?hrenS ?TLater_subst; wtcrush.
  eapply iT_ISub; last var; tcrush; [lThis|lNext]; wtcrush.
  by apply: iSub_AddI; wtcrush.
  rewrite -{3}(plusnO i). apply iLaterN_Sub; wtcrush.
Qed.

Definition anfBind t := lett t (tv x0).

Lemma AnfBind_typed Γ t (T U : ty) :
  Γ u⊢ₜ t : T →
  shift T :: Γ u⊢ₜ tv x0 : shift U →
  Γ u⊢ₜ anfBind t : U.
Proof. intros; eapply iT_Let; eauto. Qed.

Lemma pDOT_Def_Path_derived Γ l p T
  (Hx : Γ u⊢ₚ p : T, 0) :
  Γ u⊢{ l := dpt p } : TVMem l (TSing p).
Proof. eapply iD_Path, (iP_Sngl_Refl (T := T)), Hx. Qed.

(* If I add [iSub_Skolem_P] to the syntactic type system, what other rules
can I derive? Apparently, subtyping for recursive types, almost. See below! *)

Section cond.
  Context (Hskolem : ∀ Γ T1 T2 i j,
    iterate TLater i (shift T1) :: Γ u⊢ₚ pv (ids 0) : shift T2, j →
    Γ u⊢ₜ T1, i <: T2, j).
  Set Default Proof Using "Hskolem".

(* Convenient application syntax. *)
Lemma iSub_Skolem_P {Γ T1 T2 i j} :
  iterate TLater i (shift T1) :: Γ u⊢ₚ pv (ids 0) : shift T2, j →
  Γ u⊢ₜ T1, i <: T2, j.
Proof. apply Hskolem. Qed.


Lemma iMu_Sub'' {Γ T i} :
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₜ TMu (shift T), i <: T, i.
Proof.
  intros Hu; apply iSub_Skolem_P; wtcrush.
  apply (iP_LaterN (i := 0)); wtcrush; hideCtx.
  apply (iT_Mu_E' (T1 := iterate ▶:%ty i (shift (shift T)))),
    is_unstamped_TLater_n; cbn; wtcrush; last by rewrite !TLater_subst shift_sub.
  eapply iT_ISub_nocoerce; first var.
  ettrans; first apply iMu_LaterN_Sub_Distr_inv.
  rewrite (hren_upn 1 T) hrenS /=; tcrush.
Qed.

Lemma is_unstamped_ty'_upren {n T}
  (Hu : is_unstamped_ty' n.+1 T) :
  is_unstamped_ty' n.+2 T.|[up (ren (+1))].
Proof.
  rewrite up_upren_vl.
  eapply is_unstamped_sub_ren_ty, Hu.
  exact: is_unstamped_ren_up.
Qed.

Lemma iSub_Mu'' {Γ T i} :
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₜ T, i <: TMu (shift T), i.
Proof.
  intros Hu; apply iSub_Skolem_P => //.
  have HusT : is_unstamped_ty' (S (length Γ).+1) (shift T).|[up (ren (+1))].
    by apply is_unstamped_ty'_upren, is_unstamped_ren1_ty, Hu.
  apply (iP_LaterN (i := 0)); wtcrush.
  eapply iT_ISub_nocoerce, iMu_LaterN_Sub_Distr.
  apply iT_Mu_I, is_unstamped_TLater_n; cbn; wtcrush.
  by rewrite !TLater_subst (hren_upn 1) (hrenS T 1) shift_sub; var.
Qed.

(* Pretty close to [iMu_Sub_Mu'], except that the context of the hypothesis is different. *)
Lemma iMu_Sub_Mu' {Γ T1 T2 i j} :
  iterate TLater i (shift (μ T1)) :: Γ u⊢ₜ T1, i <: T2, j →
  is_unstamped_ty' (length Γ).+1 T1 →
  is_unstamped_ty' (length Γ).+1 T2 →
  Γ u⊢ₜ TMu T1, i <: TMu T2, j.
Proof.
  intros Hsub Hu1 Hu2.
  apply iSub_Skolem_P.
  have Hu1' := is_unstamped_ty'_upren Hu1.
  have Hu2' := is_unstamped_ty'_upren Hu2.
  eapply (iP_LaterN (i := 0)); tcrush.
  hideCtx.
  eapply iT_ISub_nocoerce, iMu_LaterN_Sub_Distr.
  eapply iT_Mu_I; last by wtcrush.
  rewrite TLater_subst.
  rewrite (_ : T2.|[up (ren (+1))].|[x0/] = T2); last
    by rewrite up_sub_compose; autosubst.
  have Hx0 : Γ0 u⊢ₜ x0 : iterate ▶:%ty i T1. {
    eapply iT_Mu_E'.
    by eapply iT_ISub_nocoerce, iMu_LaterN_Sub_Distr_inv; var.
    by rewrite TLater_subst up_sub_compose; autosubst.
    exact: is_unstamped_TLater_n.
  }
  eapply (iT_ISub (i := 0)), Hx0.
  apply iLaterN_Sub_LaterN, Hsub.
Qed.

Lemma iAnd_Mu Γ T1 T2 i
  (Hu1 : is_unstamped_ty' (length Γ).+1 T1)
  (Hu2 : is_unstamped_ty' (length Γ).+1 T2) :
  Γ u⊢ₜ TAnd (μ T1) (μ T2), i <: μ (TAnd T1 T2), i.
Proof.
  (* Direct proof using Bind2 and Bind1 from DOT paper. *)
  (* apply iSub_Bind_2, iSub_And_split; apply iSub_Bind_1. *)
  (* The first goal reads as:
  Γ, z1 : (mu z. T1) /\ (mu z. T2), z2 : T1[z := z2] ⊢ T1[z := z2] <: T1[z := z1]
  which is unprovable.
  *)
  (* Restart. *)
  have Hu1' := is_unstamped_ty'_upren Hu1.
  have Hu2' := is_unstamped_ty'_upren Hu2.
  apply iSub_Skolem_P.
  apply iP_Mu_I'; stcrush.
  apply iP_And_I; apply iP_Mu_E' => //.
  all: apply (iP_LaterN (i := 0)); tcrush; varsub; apply iLaterN_Sub_LaterN; tcrush.
Qed.
End cond.
