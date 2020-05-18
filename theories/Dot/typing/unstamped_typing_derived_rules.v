From D Require Import tactics.
From D.Dot Require Import syn syn_lemmas ex_utils unstamped_typing.
From D.Dot Require Import unstampedness_binding.
From D.Dot Require Import path_repl_lemmas typing_stamping.
Import DBNotation.

Lemma is_unstamped_pvar i n b : i < n → is_unstamped_path n b (pv (var_vl i)).
Proof. eauto 6. Qed.
Hint Resolve is_unstamped_pvar : core.
Lemma is_unstamped_pvars i n l b : i < n → is_unstamped_ty n b (pv (var_vl i) @; l).
Proof. eauto. Qed.
Hint Resolve is_unstamped_pvars : core.
Lemma unstamped_subject_closed {Γ e T}
  (Ht : Γ u⊢ₜ e : T) :
  nclosed e (length Γ).
Proof.
  destruct (stamp_obj_ident_typed ∅ Ht); ev. exact: is_unstamped_nclosed_tm.
Qed.

Lemma var_typed_closed {Γ x T} : Γ u⊢ₜ tv (ids x) : T → x < length Γ.
Proof. by move => /unstamped_subject_closed/fv_of_val_inv/nclosed_var_lt. Qed.

(* Ltac tcrush := repeat first [ fast_done | typconstructor | stcrush ]. *)
Ltac tcrush := repeat first [ eassumption | reflexivity | typconstructor | stcrush ].

Lemma iT_All_Ex Γ e1 x2 T1 T2:
  Γ u⊢ₜ e1: TAll T1 T2 →
  Γ u⊢ₜ tv (var_vl x2) : T1 →
  is_unstamped_ty' (S (length Γ)) T2 →
  (*────────────────────────────────────────────────────────────*)
  Γ u⊢ₜ tapp e1 (tv (var_vl x2)) : T2.|[(var_vl x2)/].
Proof.
  intros He1 Hx2 Hu. have Hlx2 := var_typed_closed Hx2.
  rewrite -(psubst_subst_agree_ty (n := S (length Γ))); tcrush.
  eapply iT_All_Ex_p with (p2 := (pv (var_vl x2))); tcrush.
Qed.

Lemma iT_Mu_E {Γ x T}:
  Γ u⊢ₜ tv (var_vl x): TMu T →
  (*──────────────────────*)
  is_unstamped_ty' (S (length Γ)) T →
  Γ u⊢ₜ tv (var_vl x): T.|[(var_vl x)/].
Proof.
  move => + Hu. rewrite -(psubst_subst_agree_ty (n := S (length Γ))) // => Hx.
  by apply (iT_Path (p := pv (ids x))), iP_Mu_E, iP_Val, Hx.
Qed.

Lemma iT_Mu_I {Γ x T}:
  Γ u⊢ₜ tv (var_vl x): T.|[(var_vl x)/] →
  (*──────────────────────*)
  is_unstamped_ty' (S (length Γ)) T →
  Γ u⊢ₜ tv (var_vl x): TMu T.
Proof.
  move => + Hu. rewrite -(psubst_subst_agree_ty (n := S (length Γ))) // => Hx.
  by apply (iT_Path (p := pv (ids x))), iP_Mu_I, iP_Val, Hx.
Qed.

Ltac tcrush ::=
  repeat first [ eassumption | reflexivity |
  apply iT_Mu_I | apply iT_Mu_E |
  typconstructor | stcrush ].

Lemma is_unstamped_TLater_n i {n T}:
  is_unstamped_ty' n T →
  is_unstamped_ty' n (iterate TLater i T).
Proof. elim: i => [|//i IHi]; rewrite ?iterate_0 ?iterate_S //; auto. Qed.

Ltac wtcrush := repeat first [ fast_done | typconstructor | stcrush ] ; try solve [
  first [
    by eauto 3 using is_unstamped_TLater_n, is_unstamped_ren1_ty, is_unstamped_ren1_path |
    try_once is_unstamped_weaken_dm |
    try_once is_unstamped_weaken_ty |
    try_once is_unstamped_weaken_path ]; eauto].

Ltac asideLaters :=
  repeat first
    [ettrans; last (apply iSub_Later; tcrush)|
    ettrans; first (apply iLater_Sub; tcrush)].

Ltac lNext := ettrans; first apply iAnd2_Sub; tcrush.
Ltac lThis := ettrans; first apply iAnd1_Sub; tcrush.

Ltac lookup :=
  lazymatch goal with
  | |- _ u⊢ₜ ?T1, _ <: ?T2, _ =>
    let T1' := eval hnf in T1 in
    match T1' with
    | (TAnd ?T11 ?T12) =>
      (* first [unify (label_of_ty T11) (label_of_ty T2); lThis | lNext] *)
      let ls := eval cbv in (label_of_ty T11, label_of_ty T2) in
      match ls with
      | (Some ?l1, Some ?l1) => lThis
      | (Some ?l1, Some ?l2) => lNext
      end
    end
  end.
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
  Γ u⊢ₜ tv (var_vl x) : T2.
Proof. intros; subst; tcrush. Qed.

Lemma iT_Var0 Γ T :
  Γ !! 0 = Some T →
  (*──────────────────────*)
  Γ u⊢ₜ tv (var_vl 0) : T.
Proof. intros; eapply iT_Var'; by rewrite ?hsubst_id. Qed.

Ltac var := exact: iT_Var0 || exact: iT_Var'.

Lemma iT_Sub_nocoerce T1 T2 {Γ e} :
  Γ u⊢ₜ e : T1 →
  Γ u⊢ₜ T1, 0 <: T2, 0 →
  Γ u⊢ₜ e : T2.
Proof. intros. exact: (iT_Sub (i:=0)). Qed.
Hint Resolve iT_Sub_nocoerce : core.

Lemma iT_Var_Sub Γ x T1 T2 :
  Γ !! x = Some T1 →
  Γ u⊢ₜ shiftN x T1, 0 <: T2, 0 →
  (*──────────────────────*)
  Γ u⊢ₜ tv (var_vl x) : T2.
Proof. by intros; eapply iT_Sub_nocoerce; [var|]. Qed.

Lemma iT_Var0_Sub Γ T1 T2 :
  Γ !! 0 = Some T1 →
  Γ u⊢ₜ T1, 0 <: T2, 0 →
  (*──────────────────────*)
  Γ u⊢ₜ tv (var_vl 0) : T2.
Proof. intros. by eapply iT_Var_Sub; [| rewrite ?hsubst_id]. Qed.

Ltac varsub := (eapply iT_Var0_Sub || eapply iT_Var_Sub); first done.

Lemma iT_All_Ex' T2 {Γ e1 x2 T1 T3} :
  Γ u⊢ₜ e1: TAll T1 T2 →                        Γ u⊢ₜ tv (ids x2) : T1 →
  T3 = T2.|[ids x2/] →
  is_unstamped_ty' (S (length Γ)) T2 →
  (*────────────────────────────────────────────────────────────*)
  Γ u⊢ₜ tapp e1 (tv (ids x2)) : T3.
Proof. intros; subst; exact: iT_All_Ex. Qed.

Lemma iT_Mu_E' {Γ x T1 T2}:
  Γ u⊢ₜ tv (ids x): μ T1 →
  T2 = T1.|[ids x/] →
  is_unstamped_ty' (S (length Γ)) T1 →
  (*──────────────────────*)
  Γ u⊢ₜ tv (ids x): T2.
Proof. intros; subst; tcrush. Qed.

Lemma iSub_Sel' Γ U {p l L i}:
  is_unstamped_ty' (length Γ) L →
  Γ u⊢ₚ p : TTMem l L U, i →
  Γ u⊢ₜ L, i <: TSel p l, i.
Proof. intros; ettrans; last exact: (@iSub_Sel _ p); tcrush. Qed.

(** Specialization of [iSub_Sel'] for convenience. *)
Lemma iSub_Sel'' Γ {p l L i}:
  is_unstamped_ty' (length Γ) L →
  Γ u⊢ₚ p : TTMem l L L, i → Γ u⊢ₜ L, i <: TSel p l, i.
Proof. apply iSub_Sel'. Qed.

(* Worse than iD_Typ_Abs, but shown in the paper. *)
(* Lemma iD_Typ_Abs_intermediate Γ T l L U:
  is_unstamped_ty' (length Γ) L →
  is_unstamped_ty' (length Γ) T →
  is_unstamped_ty' (length Γ) U →
  Γ u⊢ₜ L, 0 <: T, 0 →
  Γ u⊢ₜ T, 0 <: U, 0 →
  Γ u⊢{ l := dtysyn T } : TTMem l L U.
Proof. intros; apply iD_Typ_Abs => //; tcrush; exact: iSub_Mono. Qed. *)

(** * Manipulating laters, basics. *)

Lemma iSub_AddIJ {Γ T} i j (Hst: is_unstamped_ty' (length Γ) T) :
  Γ u⊢ₜ T, j <: T, i + j.
Proof.
  elim: i => [|n IHn]; first tcrush.
  ettrans; first apply IHn.
  ettrans; [exact: iSub_Add_Later | tcrush].
Qed.

Lemma iSub_AddIJ' {Γ T} i j (Hst: is_unstamped_ty' (length Γ) T) (Hle : i <= j) :
  Γ u⊢ₜ T, i <: T, j.
Proof. rewrite (le_plus_minus i j Hle) Nat.add_comm. exact: iSub_AddIJ. Qed.

Lemma iSub_AddI Γ T i (Hst: is_unstamped_ty' (length Γ) T) :
  Γ u⊢ₜ T, 0 <: T, i.
Proof. apply (iSub_AddIJ' 0 i); by [|lia]. Qed.

Lemma path_tp_delay {Γ p T i j} (Hst: is_unstamped_ty' (length Γ) T) : i <= j →
  Γ u⊢ₚ p : T, i → Γ u⊢ₚ p : T, j.
Proof.
  intros Hle Hp.
  rewrite (le_plus_minus i j Hle); move: {j Hle} (j - i) => k.
  eapply iP_Sub, Hp.
  apply: iSub_AddIJ'; by [|lia].
Qed.

(* Lemma AddIB_stp Γ T U i:
  is_unstamped_ty' (length Γ) T →
  is_unstamped_ty' (length Γ) U →
  Γ u⊢ₜ T, 0 <: U, 0 →
  Γ u⊢ₜ T, i <: U, i.
Proof.
  move => HuT HuU Hstp; elim: i => [|n IHn]; first tcrush.
  exact: iSub_Mono.
Qed. *)

(** * Derived constructions. *)

Lemma iT_Let Γ t u T U :
  Γ u⊢ₜ t : T →
  shift T :: Γ u⊢ₜ u : shift U →
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₜ lett t u : U.
Proof. move => Ht Hu HsT. apply /iT_All_E /Ht /iT_All_I /Hu /HsT. Qed.

Lemma val_LB L U Γ i x l :
  is_unstamped_ty' (length Γ) L →
  is_unstamped_ty' (length Γ) U →
  x < length Γ →
  Γ u⊢ₜ tv (ids x) : type l >: L <: U →
  Γ u⊢ₜ ▶: L, i <: (pv (ids x) @; l), i.
Proof.
  intros ??? Hv; apply (iSub_Sel (p := pv _) (U := U)).
  apply (path_tp_delay (i := 0)); wtcrush.
Qed.

Lemma val_UB L U Γ i x l :
  is_unstamped_ty' (length Γ) L →
  is_unstamped_ty' (length Γ) U →
  x < length Γ →
  Γ u⊢ₜ tv (ids x) : type l >: L <: U →
  Γ u⊢ₜ (pv (ids x) @; l), i <: ▶: U, i.
Proof.
  intros ??? Hv; apply (iSel_Sub (p := pv _) (L := L)).
  apply (path_tp_delay (i := 0)); wtcrush.
Qed.

(* These rules from storeless typing must be encoded somehow via variables. *)
(* Lemma packTV_LB T n Γ i :
  is_unstamped_ty' n T →
  n <= length Γ →
  Γ u⊢ₜ ▶: T, i <: (pv (packTV T) @; "A"), i.
Proof. intros; apply /val_LB /packTV_typed'. Qed. *)

(* Lemma packTV_UB T n Γ i :
  is_unstamped_ty' n T →
  n <= length Γ →
  Γ u⊢ₜ (pv (packTV T) @; "A"), i <: ▶: T, i.
Proof. intros; by apply /val_UB /packTV_typed'. Qed. *)

Lemma iD_Typ Γ T l:
  is_unstamped_ty' (length Γ) T →
  Γ u⊢{ l := dtysyn T } : TTMem l T T.
Proof. intros. tcrush. Qed.

(* We can derive rules iSub_Bind_1 and iSub_Bind_2 (the latter only conjectured) from
  "Type Soundness for Dependent Object Types (DOT)", Rompf and Amin, OOPSLA '16. *)
Lemma iSub_Bind_1 Γ T1 T2 i:
  is_unstamped_ty' (S (length Γ)) T1 → is_unstamped_ty' (length Γ) T2 →
  iterate TLater i T1 :: Γ u⊢ₜ T1, i <: shift T2, i →
  Γ u⊢ₜ μ T1, i <: T2, i.
Proof.
  intros Hus1 Hus2 Hsub.
  ettrans; first exact: (iMu_Sub_Mu Hsub).
  exact: iMu_Sub.
Qed.

Lemma iSub_Bind_2 Γ T1 T2 i:
  is_unstamped_ty' (length Γ) T1 → is_unstamped_ty' (S (length Γ)) T2 →
  iterate TLater i (shift T1) :: Γ u⊢ₜ shift T1, i <: T2, i →
  Γ u⊢ₜ T1, i <: μ T2, i.
Proof.
  intros Hus1 Hus2 Hsub.
  ettrans; last apply (iMu_Sub_Mu Hsub); [exact: iSub_Mu | wtcrush].
Qed.

Lemma iSub_Bind_1' Γ T1 T2:
  is_unstamped_ty' (S (length Γ)) T1 → is_unstamped_ty' (length Γ) T2 →
  T1 :: Γ u⊢ₜ T1, 0 <: shift T2, 0 →
  Γ u⊢ₜ μ T1, 0 <: T2, 0.
Proof. intros; exact: iSub_Bind_1. Qed.

Lemma iSub_Bind_2' Γ T1 T2:
  is_unstamped_ty' (length Γ) T1 → is_unstamped_ty' (S (length Γ)) T2 →
  shift T1 :: Γ u⊢ₜ shift T1, 0 <: T2, 0 →
  Γ u⊢ₜ T1, 0 <: μ T2, 0.
Proof. intros; exact: iSub_Bind_2. Qed.

Ltac mltcrush := tcrush; try ((apply iSub_Bind_1' || apply iSub_Bind_1); tcrush); repeat lookup.

(* Simplified package introduction, for talk. *)
Lemma BindSpec Γ (L T U : ty):
  is_unstamped_ty' (S (length Γ)) T →
  is_unstamped_ty' (S (length Γ)) L → is_unstamped_ty' (S (length Γ)) U →
  {@ type "A" >: T <: T }%ty :: Γ u⊢ₜ L, 1 <: T, 1 →
  {@ type "A" >: T <: T }%ty :: Γ u⊢ₜ T, 1 <: U, 1 →
  Γ u⊢ₜ tv (ν {@ type "A" = T }) : μ {@ type "A" >: L <: U }.
Proof.
  intros.
  eapply iT_Sub_nocoerce with (T1 := μ {@ type "A" >: T <: T }); ltcrush.
Qed.

Lemma iP_Sub' {Γ p T1 T2 i} :
  Γ u⊢ₜ T1, i <: T2, i →
  Γ u⊢ₚ p : T1, i →
  (*───────────────────────────────*)
  Γ u⊢ₚ p : T2, i.
Proof.
  intros; rewrite -(plusnO i).
  by eapply iP_Sub; rewrite ?plusnO.
Qed.

Lemma iP_Sngl_Sym Γ p q i:
  is_unstamped_path' (length Γ) q →
  Γ u⊢ₚ p : TSing q, i →
  Γ u⊢ₚ q : TSing p, i.
Proof.
  intros Hus Hpq. eapply iP_Sub'.
  eapply (iSngl_Sub_Sym Hpq). by apply iSngl_Sub_Self, Hpq.
  eapply iP_Sngl_Refl.
  by apply (iP_Sngl_Inv Hpq).
Qed.

Lemma iSngl_pq_Sub_inv {Γ i p q T1 T2}:
  T1 ~Tp[ p := q ]* T2 →
  is_unstamped_ty' (length Γ) T1 →
  is_unstamped_ty' (length Γ) T2 →
  is_unstamped_path' (length Γ) p →
  Γ u⊢ₚ q : TSing p, i →
  Γ u⊢ₜ T1, i <: T2, i.
Proof. intros. by eapply iSngl_pq_Sub, iP_Sngl_Sym. Qed.

Lemma iP_And {Γ p T1 T2 i}:
  Γ u⊢ₚ p : T1, i →
  Γ u⊢ₚ p : T2, i →
  Γ u⊢ₚ p : TAnd T1 T2, i.
Proof.
  intros Hp1 Hp2. eapply iP_Sub', iP_Sngl_Refl, Hp1.
  apply iSub_And; exact: iSngl_Sub_Self.
Qed.

Lemma iMu_Sub' {Γ T T' i}:
  T' = shift T →
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₜ μ T', i <: T, i.
Proof. intros; subst. auto. Qed.

Lemma iD_Lam_Sub {Γ} V T1 T2 e l L:
  shift T1 :: V :: Γ u⊢ₜ e : T2 →
  TLater V :: Γ u⊢ₜ TAll T1 T2, 0 <: L, 0 →
  is_unstamped_ty' (S (length Γ)) T1 →
  Γ |L V u⊢{ l := dpt (pv (vabs e)) } : TVMem l L.
Proof.
  intros He Hsub Hs. apply iD_Val.
  eapply (iT_Sub (i := 0)); first apply Hsub.
  by apply iT_All_I_strip1.
Qed.

Lemma iD_Path_Sngl {Γ} p l T :
  Γ u⊢ₚ p : T, 0 →
  Γ u⊢{ l := dpt p } : TVMem l (TSing p).
Proof. intros Hp. eapply iD_Path, iP_Sngl_Refl, Hp. Qed.

(* Note how we must weaken the type (or its environment) to account for the
   self-variable of the created object. *)
Definition packTV l T := (ν {@ type l = shift T }).

Lemma packTV_typed' T n Γ l :
  is_unstamped_ty' n T →
  n <= length Γ →
  Γ u⊢ₜ tv (packTV l T) : typeEq l T.
Proof.
  move => HsT1 Hle; move: (Hle) (HsT1) => /le_n_S Hles /is_unstamped_ren1_ty HsT2.
  apply (iT_Sub_nocoerce (μ {@ typeEq l (shift T) }));
    last (ettrans; first apply: (iMu_Sub _ (T := {@ typeEq l T })); wtcrush).
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
  is_unstamped_ty' (S (length Γ)) U →
  Γ u⊢ₜ tyApp t l T : V.
Proof.
  move => Ht Hsub HuT1 HuU1.
  eapply iT_Let; [exact: Ht| |wtcrush].
  eapply iT_Let; [apply packTV_typed| |]; wtcrush.
  rewrite /= -!hrenS -/(typeEq _ _).

  apply /iT_Sub_nocoerce /Hsub.

  eapply iT_All_Ex'; first var.
  have HuT3 : is_unstamped_ty' (S (S (length Γ))) (shiftN 2 T)
    by rewrite hrenS; wtcrush.
  varsub; tcrush; rewrite !hsubst_comp; f_equal. autosubst.
  asimpl.
  eapply is_unstamped_sub_ren_ty, HuU1.
  by move => [|i] Hi //=; [constructor => /=| eauto].
Qed.

(** * Manipulating laters, more.

 *)
Lemma iSub_LaterN Γ T i j:
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₜ T, j + i <: iterate TLater j T, i.
Proof.
  elim: j T => /= [|j IHj] T HuT; rewrite ?iterate_0 ?iterate_Sr /=; tcrush.
  ettrans.
  - exact: iSub_Later.
  - apply (IHj (TLater T)); stcrush.
Qed.

Lemma iLaterN_Sub {Γ T} i j :
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₜ iterate TLater j T, i <: T, j + i.
Proof.
  elim: j T => /= [|j IHj] T HuT; rewrite ?iterate_0 ?iterate_Sr /=; tcrush.
  ettrans.
  - apply (IHj (TLater T)); stcrush.
  - exact: iLater_Sub.
Qed.

(* This can be useful when [T] is a singleton type. *)
Lemma dropLaters Γ e T U i:
  Γ u⊢ₜ e : T →
  Γ u⊢ₜ T, 0 <: iterate TLater i U, 0 →
  is_unstamped_ty' (length Γ) T →
  is_unstamped_ty' (length Γ) U →
  Γ u⊢ₜ iterate tskip i e : TAnd T U.
Proof.
  intros HeT Hsub HuT HuU.
  eapply iT_Sub, HeT => {HeT}.
  typconstructor; [exact: iSub_AddI|] => {HuT}.
  ettrans; [apply: Hsub|] => {Hsub}.
  have := (iLaterN_Sub 0 i HuU); rewrite plusnO; exact.
Qed.

(**
  Like [let: x := e1 in e2], but dropping [i] laters from [e1]'s type while
  preserving its identity by adding a singleton type. See
*)
Definition deLater e1 i e2 := lett e1 (lett (iterate tskip i (tv x0)) e2).

Lemma deLaterSingV0 {Γ} p i e T U:
  Γ u⊢ₚ p : TSing p, 0 →
  shift (TSing p) :: Γ u⊢ₜ shift (TSing p), 0 <: iterate TLater i T, 0 →
  TAnd (TSing (shiftN 2 p)) (shift T) :: TSing (shift p) :: Γ u⊢ₜ e : shiftN 2 U →
  is_unstamped_ty' (length Γ) T →
  is_unstamped_path' (length Γ) p →
  Γ u⊢ₜ deLater (path2tm p) i e : U.
Proof.
  intros HpT1 Hsub HeU HuT Hup.
  apply iT_Let with (T := TSing p); tcrush.
  apply iT_Let with (T := TAnd (shift (TSing p)) T); rewrite /= -?hrenS; wtcrush.
  apply dropLaters; [ var | .. ]; rewrite /= -?hrenS; wtcrush.
Qed.

(** More general version of [deLaterSingV0]. Not sure if too general or useful. *)
Lemma deLaterSingV1 {Γ} p i e T1 T2 U:
  Γ u⊢ₚ p : T1, 0 →
  shift (TAnd (TSing p) T1) :: Γ u⊢ₜ shift T1, 0 <: iterate TLater i T2, 0 →
  TAnd (TAnd (TSing (shiftN 2 p)) (shiftN 2 T1)) (shift T2) ::
    TAnd (TSing (shift p)) (shift T1) :: Γ u⊢ₜ e : shiftN 2 U →
  is_unstamped_ty' (length Γ) T1 →
  is_unstamped_ty' (length Γ) T2 →
  is_unstamped_path' (length Γ) p →
  Γ u⊢ₜ deLater (path2tm p) i e : U.
Proof.
  intros HpT1 Hsub HeU HuT1 HuT2 Hup.
  apply iT_Let with (T := TAnd (TSing p) T1); tcrush.
  by apply iP_And, HpT1; eapply iP_Sngl_Refl, HpT1.
  apply iT_Let with (T := TAnd (shift (TAnd (TSing p) T1)) T2); rewrite /= -?hrenS; wtcrush.
  apply dropLaters; [ var | lNext | ..]; rewrite /= -?hrenS; wtcrush.
Qed.

(** Best version of [deLaterSing]. *)
Lemma deLaterSing {Γ} p i e T1 U:
  Γ u⊢ₚ p : iterate TLater i T1, 0 →
  TAnd (TSing (shiftN 2 p)) (shiftN 2 T1) ::
    TAnd (TSing (shift p)) (iterate TLater i (shift T1)) :: Γ u⊢ₜ e : shiftN 2 U →
  is_unstamped_ty' (length Γ) T1 →
  is_unstamped_path' (length Γ) p →
  Γ u⊢ₜ deLater (path2tm p) i e : U.
Proof.
  intros HpT1 HeU HuT1 Hup.
  apply iT_Let with (T := TAnd (TSing p) (iterate TLater i T1)); wtcrush.
  by apply iP_And, HpT1; eapply iP_Sngl_Refl, HpT1.
  apply iT_Let with (T := TAnd (TSing (shift p)) (shift T1));
    rewrite /= -?hrenS ?TLater_subst; wtcrush.
  eapply iT_Sub; last var; tcrush; [lThis|lNext]; wtcrush.
  by apply: iSub_AddI; wtcrush.
  rewrite -{3}(plusnO i). apply iLaterN_Sub; wtcrush.
Qed.

Lemma selfIntersect Γ T U i j:
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₜ T, i <: U, j + i →
  Γ u⊢ₜ T, i <: TAnd U T, j + i .
Proof. intros; tcrush. exact: iSub_AddIJ. Qed.

Lemma iAnd_Later_Sub_Distr Γ T1 T2 i :
  is_unstamped_ty' (length Γ) T1 →
  is_unstamped_ty' (length Γ) T2 →
  Γ u⊢ₜ TAnd (TLater T1) (TLater T2), i <: TLater (TAnd T1 T2), i.
Proof. intros; asideLaters; tcrush; [lThis|lNext]. Qed.

(** Inverse of [iAnd_Later_Sub_Distr]. *)
Lemma iAnd_Later_Sub_Distr_inv Γ T1 T2 i :
  is_unstamped_ty' (length Γ) T1 →
  is_unstamped_ty' (length Γ) T2 →
  Γ u⊢ₜ TLater (TAnd T1 T2), i <: TAnd (TLater T1) (TLater T2), i.
Proof. intros; tcrush. Qed.

Lemma iOr_Later_Sub_Distr Γ T1 T2 i :
  is_unstamped_ty' (length Γ) T1 →
  is_unstamped_ty' (length Γ) T2 →
  Γ u⊢ₜ TOr (TLater T1) (TLater T2), i <: TLater (TOr T1 T2), i.
Proof. intros; tcrush. Qed.

(** Inverse of [iOr_Later_Sub_Distr]. *)
Lemma iOr_Later_Sub_Distr_inv Γ T1 T2 i :
  is_unstamped_ty' (length Γ) T1 →
  is_unstamped_ty' (length Γ) T2 →
  Γ u⊢ₜ TLater (TOr T1 T2), i <: TOr (TLater T1) (TLater T2), i.
Proof.
  intros; asideLaters; typconstructor; ettrans;
    [| apply iSub_Or1 | | apply iSub_Or2]; tcrush.
Qed.

(** TLater swaps with TMu, part 1. *)
Lemma iMu_Later_Sub_Distr Γ T i :
  is_unstamped_ty' (S (length Γ)) T →
  Γ u⊢ₜ TMu (TLater T), i <: TLater (TMu T), i.
Proof. intros; asideLaters; tcrush. Qed.

(** TLater swaps with TMu, part 2. *)
Lemma iMu_Later_Sub_Distr_inv Γ T i :
  is_unstamped_ty' (S (length Γ)) T →
  Γ u⊢ₜ TLater (TMu T), i <: TMu (TLater T), i.
Proof. intros; asideLaters; tcrush. Qed.

(** Show that [singleton_Mu_[12]] and [iP_Mu_[IE]] are interderivable. *)
Lemma singleton_Mu_1 {Γ p T i} :
  Γ u⊢ₚ p : TMu T, i →
  is_unstamped_ty' (S (length Γ)) T →
  Γ u⊢ₜ TSing p, i <: T .Tp[ p /], i.
Proof. intros Hp Hu; apply iSngl_Sub_Self, (iP_Mu_E Hu Hp). Qed.

Lemma singleton_Mu_2 {Γ p T i} :
  Γ u⊢ₚ p : T .Tp[ p /], i →
  is_unstamped_ty' (S (length Γ)) T →
  Γ u⊢ₜ TSing p, i <: TMu T, i.
Proof. intros Hp Hu; apply iSngl_Sub_Self, (iP_Mu_I Hu Hp). Qed.

(* Avoid automation, to ensure we don't use [iP_Mu_E] to show them. *)
Lemma iP_Mu_E' {Γ T p i} :
  Γ u⊢ₚ p : TMu T, i →
  is_unstamped_ty' (S (length Γ)) T →
  Γ u⊢ₚ p : T .Tp[ p /], i.
Proof.
  intros Hp Hu. eapply iP_Sub', (iP_Sngl_Refl Hp).
  apply (singleton_Mu_1 Hp Hu).
Qed.

Lemma iP_Mu_I' {Γ T p i} :
  Γ u⊢ₚ p : T .Tp[ p /], i →
  is_unstamped_ty' (S (length Γ)) T →
  Γ u⊢ₚ p : TMu T, i.
Proof.
  intros Hp Hu. eapply iP_Sub', (iP_Sngl_Refl Hp).
  apply (singleton_Mu_2 Hp Hu).
Qed.

(**
Show soundness of subtyping for recursive types in the Dotty compiler — just cases in subtype checking.

The first case is in
https://github.com/lampepfl/dotty/blob/0.20.0-RC1/compiler/src/dotty/tools/dotc/core/TypeComparer.scala#L550-L552
And that matches iMu_Sub_Mu.

https://github.com/lampepfl/dotty/blob/0.20.0-RC1/compiler/src/dotty/tools/dotc/core/TypeComparer.scala#L554-L557
We formalize that as the derived rule below.

The action of [fixRecs] depends on the type [T1] of [p].
Hence, here we we assume the action of [fixRecs] has already been carried out:
to do that, one must unfold top-level recursive types in the type of [p],
as allowed through [P_Mu_E], rules for intersection types and intersection introduction.
On the other hand, this derived rule handles the substitution in [T2] directly.
*)
Lemma singleton_Mu_dotty1 {Γ p i T1' T2} :
  Γ u⊢ₜ T1', i <: T2 .Tp[ p /], i →
  Γ u⊢ₚ p : T1', i →
  is_unstamped_ty' (S (length Γ)) T2 →
  Γ u⊢ₜ TSing p, i <: TMu T2, i.
Proof.
  intros Hsub Hp Hu.
  apply singleton_Mu_2, Hu.
  apply (iP_Sub' Hsub Hp).
Qed.

Definition anfBind t := lett t (tv x0).

Lemma AnfBind_typed Γ t (T U: ty) :
  Γ u⊢ₜ t : T →
  shift T :: Γ u⊢ₜ tv x0 : shift U →
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₜ anfBind t : U.
Proof. intros; eapply iT_Let; eauto. Qed.

Lemma pDOT_Def_Path_derived Γ l p T
  (Hx : Γ u⊢ₚ p : T, 0):
  Γ u⊢{ l := dpt p } : TVMem l (TSing p).
Proof. eapply iD_Path, (iP_Sngl_Refl (T := T)), Hx. Qed.

Lemma iP_LaterN {Γ p T i j} :
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₚ p : iterate TLater j T, i →
  Γ u⊢ₚ p : T, i + j.
Proof.
  elim: j i => [|j IHj] i Hu Hp; rewrite (plusnO, plusnS); first done.
  apply (IHj (S i)), iP_Later, Hp; tcrush; exact: is_unstamped_TLater_n.
Qed.

Lemma iMu_LaterN_Sub_Distr_inv {Γ T i n} :
  is_unstamped_ty' (S (length Γ)) T →
  Γ u⊢ₜ iterate TLater n (TMu T), i <: TMu (iterate TLater n T), i.
Proof.
  intros Hu.
  elim: n i => [|n IHn] i; first tcrush; rewrite !iterate_S.
  ettrans; last apply iMu_Later_Sub_Distr_inv.
  by asideLaters; wtcrush.
  by apply is_unstamped_TLater_n; stcrush.
Qed.

Lemma iMu_LaterN_Sub_Distr {Γ T i n} :
  is_unstamped_ty' (S (length Γ)) T →
  Γ u⊢ₜ TMu (iterate TLater n T), i <: iterate TLater n (TMu T), i.
Proof.
  intros Hu.
  elim: n i => [|n IHn] i; first tcrush; rewrite !iterate_S.
  ettrans; first apply iMu_Later_Sub_Distr.
  by apply is_unstamped_TLater_n; stcrush.
  by asideLaters; wtcrush.
Qed.

(* If I add [iSub_Skolem_P] to the syntactic type system, what other rules
can I derive? Apparently, subtyping for recursive types, almost. See below! *)

Set Suggest Proof Using.
Section cond.
  Context (Hskolem : ∀ Γ T1 T2 i j,
    is_unstamped_ty' (length Γ) T1 →
    iterate TLater i (shift T1) :: Γ u⊢ₚ pv (ids 0) : shift T2, j →
    Γ u⊢ₜ T1, i <: T2, j).
  Set Default Proof Using "Hskolem".

(* Convenient application syntax. *)
Lemma iSub_Skolem_P {Γ T1 T2 i j}:
  is_unstamped_ty' (length Γ) T1 →
  iterate TLater i (shift T1) :: Γ u⊢ₚ pv (ids 0) : shift T2, j →
  Γ u⊢ₜ T1, i <: T2, j.
Proof. apply Hskolem. Qed.


Lemma iMu_Sub'' {Γ T i}:
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₜ TMu (shift T), i <: T, i.
Proof.
  intros Hu; apply iSub_Skolem_P; wtcrush.
  apply (iP_LaterN (i := 0)); wtcrush; hideCtx.
  apply (iT_Mu_E' (T1 := iterate ▶:%ty i (shift (shift T)))),
    is_unstamped_TLater_n; cbn; wtcrush; last by rewrite !TLater_subst shift_sub.
  eapply iT_Sub_nocoerce; first var.
  ettrans; first apply iMu_LaterN_Sub_Distr_inv; first
    by rewrite (hren_upn 1); eapply is_unstamped_sub_ren_ty, Hu; auto.
  rewrite (hren_upn 1 T) hrenS /=; tcrush; cbn.
  by apply is_unstamped_TLater_n; wtcrush.
Qed.

Lemma iSub_Mu'' {Γ T i}:
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₜ T, i <: TMu (shift T), i.
Proof.
  intros Hu; apply iSub_Skolem_P => //.
  have HusT: is_unstamped_ty' (S (S (length Γ))) (shift T).|[up (ren (+1))]
    by rewrite (hren_upn 1); eapply is_unstamped_sub_ren_ty, Hu; auto.
  apply (iP_LaterN (i := 0)); wtcrush.
  eapply iT_Sub_nocoerce, iMu_LaterN_Sub_Distr; last by wtcrush.
  apply iT_Mu_I, is_unstamped_TLater_n; cbn; wtcrush.
  by rewrite !TLater_subst (hren_upn 1) (hrenS T 1) shift_sub; var.
Qed.

(* Pretty close to [iMu_Sub_Mu'], except that the context of the hypothesis is different. *)
Lemma iMu_Sub_Mu' {Γ T1 T2 i j}:
  iterate TLater i (shift (μ T1)) :: Γ u⊢ₜ T1, i <: T2, j →
  is_unstamped_ty' (S (length Γ)) T1 →
  is_unstamped_ty' (S (length Γ)) T2 →
  Γ u⊢ₜ TMu T1, i <: TMu T2, j.
Proof.
  intros Hsub Hu1 Hu2.
  apply iSub_Skolem_P; stcrush.
  have Hu1' : is_unstamped_ty' (S (S (length Γ))) T1.|[up (ren (+1))]. {
    rewrite up_upren_vl.
    eapply is_unstamped_sub_ren_ty, Hu1.
    by apply is_unstamped_ren_up.
  }
  have Hu2' : is_unstamped_ty' (S (S (length Γ))) T2.|[up (ren (+1))]. {
    rewrite up_upren_vl.
    eapply is_unstamped_sub_ren_ty, Hu2.
    by apply is_unstamped_ren_up.
  }
  eapply (iP_LaterN (i := 0)); wtcrush.
  hideCtx.
  eapply iT_Sub_nocoerce, iMu_LaterN_Sub_Distr, Hu2'.
  eapply iT_Mu_I; last by wtcrush.
  rewrite TLater_subst.
  rewrite (_ : T2.|[up (ren (+1))].|[x0/] = T2); last
    by rewrite up_sub_compose; autosubst.
  have Hx0 : Γ0 u⊢ₜ x0 : iterate ▶:%ty i T1. {
    eapply iT_Mu_E'.
    by eapply iT_Sub_nocoerce, iMu_LaterN_Sub_Distr_inv; [var|done].
    by rewrite TLater_subst up_sub_compose; autosubst.
    exact: is_unstamped_TLater_n.
  }
  eapply (iT_Sub (i := 0)), Hx0.
  ettrans; first apply iLaterN_Sub; first wtcrush.
  ettrans; last apply iSub_LaterN, Hu2.
  rewrite !plusnO.
  exact: Hsub.
Qed.

End cond.
