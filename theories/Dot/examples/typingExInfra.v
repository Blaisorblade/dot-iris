(**
Infrastructure for examples of DOT programs using stamped and storeless typing.
*)
From stdpp Require Import strings gmap.

From D Require Import tactics.
From D.Dot Require Import syn.
From D.Dot Require Export typing_storeless exampleInfra hoas.
Export DBNotation.

Set Default Proof Using "Type".
Set Suggest Proof Using.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).
Implicit Types (g : stys).

(**********************)
(** STAMPED NOTATION **)
(**********************)
Bind Scope positive_scope with stamp.

Notation σ1 := ([] : vls).
Notation s1 := (1 %positive).

Notation σ2 := ([] : vls).
Notation s2 := (2 %positive).

Notation "'type' l = ( σ ; s )" := (l, dtysem σ s) (at level 60, l at level 50).

(***************)
(** WEAKENING **)
(***************)
From D.Dot Require Import traversals stampingDefsCore typeExtractionSyn.

Lemma extr_dtysem_stamped {g s} σ T n :
  T ~[ n ] (g, (s, σ)) →
  is_stamped_σ n g σ →
  is_stamped_dm n g (dtysem σ s).
Proof.
  rewrite /= /extraction => -[T' [Hg [Hs [Hclσ HstT']]]].
  by apply @Trav1.trav_dtysem with (T' := T') (ts' := (length σ, g)).
Qed.

Lemma extraction_weaken m n T gsσ :
  T ~[ n ] gsσ → n <= m → T ~[ m ] gsσ.
Proof.
  move: gsσ => [g [s σ]] /= [T' ?] Hle; ev.
  exists T'; split_and!; eauto using is_stamped_weaken_σ.
Qed.

(* While other lemmas allow to produce a suitable stamp table, for examples it makes more sense to have a generic one. *)
Lemma pack_extraction g s T n σ :
  g !! s = Some T →
  is_stamped_ty n g T →
  σ = idsσ n →
  T ~[ n ] (g, (s, σ)).
Proof.
  move => Hcl Hl ->; exists T; move: (is_stamped_nclosed_ty Hl) => Hst.
  rewrite length_idsσ closed_subst_idsρ; auto.
Qed.

Lemma pack_extraction' g s T T' n σ :
  g !! s = Some T →
  is_stamped_ty (length σ) g T →
  is_stamped_σ n g σ →
  T' = T.|[∞ σ] →
  T' ~[ n ] (g, (s, σ)).
Proof. move => Hcl HsT Hsσ ->. exists T; split_and!; auto. Qed.

Notation styConforms' g p := (g !! pStamp p = Some (pTy p)).
Definition styConforms {nvl} g (p : preTyMem nvl) : Prop := styConforms' g p.
Arguments styConforms {_} _ !_ /.

Record TyMemStamp g p := {
  pStampTy : is_stamped_ty (length (pSubst p)) g (pTy p); pStampσ: is_stamped_σ (pNoVars p) g (pSubst p);
}.

Notation extractPreTyMem' g p := ((pTy p).|[∞ pSubst p] ~[ pNoVars p ] (g, (pStamp p, pSubst p))).
Definition extractPreTyMem g (p : stampTy): Prop := extractPreTyMem' g p.

Lemma stampTyAgree g : ∀ p, styConforms' g p → TyMemStamp g p → extractPreTyMem' g p.
Proof. move=> [s σ T n]/= Hl [/= HsT Hsσ]. exact: pack_extraction'. Qed.

(** wrappers for [hstampTy], which is more convenient for HOAS terms. *)
Definition stClose : hstampTy → stampTy := λ '(MkTy s hσ T n), (MkTy s (map hclose hσ) T n).

Definition hTyMemStamp g p := TyMemStamp g (stClose p).
Arguments hTyMemStamp _ !_ /.

Notation hextractPreTyMem' g p := (extractPreTyMem' g (stClose p)).
Definition hextractPreTyMem g (p : hstampTy) := hextractPreTyMem' g p.

Lemma hstampTyAgree g p: styConforms' g p → hTyMemStamp g p → hextractPreTyMem' g p.
Proof. intros; apply stampTyAgree => //. by destruct p. Qed.

Definition pToStys {nvl} : preTyMem nvl → stys := λ '(MkTy s σ T n), {[s:=T]}.
Definition pAddStys {nvl} : preTyMem nvl → stys → stys := λ p g, pToStys p ∪ g.
Global Arguments pAddStys {_} !_ /.

Lemma pAddStysSpec {nvl} g s σ T n :
  pAddStys (nvl := nvl) (MkTy s σ T n) g = <[s:=T]> g.
Proof. by rewrite insert_union_singleton_l. Qed.
Lemma pAddStysConforms {nvl} g p : styConforms (nvl := nvl) (pAddStys p g) p.
Proof.
  destruct p; simpl. apply /lookup_union_Some_raw /ltac:(left) /lookup_insert.
Qed.

Definition psAddStys {nvl} : stys → list (preTyMem nvl) → stys := foldr pAddStys.
(* XXX prove its correctness, or just test it via vm_compute? *)

(****************)
(** AUTOMATION **)
(****************)
(* Prevent simplification from unfolding it, basically unconditionally. *)
Arguments extraction : simpl never.

(* For performance, keep these hints local to examples *)
Hint Extern 5 => try_once extraction_weaken : core.
Hint Extern 5 (is_stamped_ty _ _ _) => try_once is_stamped_weaken_ty : core.
Hint Extern 5 (is_stamped_dm _ _ _) => try_once is_stamped_weaken_dm : core.
Hint Extern 5 (is_stamped_ren _ _ _ _) => progress cbn : core.

(** [tcrush] is the safest automation around. *)
Ltac tcrush := repeat first [ eassumption | reflexivity | typconstructor | stcrush ].
Ltac wtcrush := repeat first [fast_done | typconstructor | stcrush]; try solve [ done |
  first [
    (* by eauto 3 using is_stamped_TLater_n, is_stamped_ren1_ty, is_stamped_ren1_path *)
    by eauto 3 using is_stamped_ren1_ty |
    try_once extraction_weaken |
    try_once is_stamped_weaken_dm |
    try_once is_stamped_weaken_ty ]; eauto ].

Hint Extern 5 (nclosed _ _) => by solve_fv_congruence : fvc.
Hint Resolve pack_extraction : fvc.
Hint Extern 5 (is_stamped_ty _ _ _) => tcrush : fvc.
Hint Extern 5 (is_stamped_σ _ _ _) => tcrush : fvc.
Hint Resolve pack_extraction' : fvc.
Ltac by_extcrush := by try eapply pack_extraction'; rewrite /= ?hsubst_id; eauto with fvc.

Ltac hideCtx :=
  let hideCtx' Γ := (let x := fresh "Γ" in set x := Γ) in
  match goal with
  | |- ?Γ v⊢ₜ[ _ ] _ : _ => hideCtx' Γ
  | |- ?Γ v⊢ₜ[ _ ] _, _ <: _, _ => hideCtx' Γ
  | |- ?Γ v⊢ₚ[ _ ] _ : _, _  => hideCtx' Γ
  | |- ?Γ v⊢[ _ ]{ _ := _  } : _ => hideCtx' Γ
  | |- ?Γ v⊢ds[ _ ] _ : _ => hideCtx' Γ
  end.

Hint Constructors typed subtype dms_typed dm_typed path_typed : core.
Remove Hints iSub_Trans : core.
Hint Extern 10 => try_once iSub_Trans : core.


(** Not used here, but useful for extending storeless typing and making it compositional. *)
Lemma storeless_typing_mono_mut Γ g :
  (∀ e T, Γ v⊢ₜ[ g ] e : T → ∀ g' (Hle : g ⊆ g'), Γ v⊢ₜ[ g' ] e : T) ∧
  (∀ ds T, Γ v⊢ds[ g ] ds : T → ∀ g' (Hle : g ⊆ g'), Γ v⊢ds[ g' ] ds : T) ∧
  (∀ l d T, Γ v⊢[ g ]{ l := d } : T → ∀ g' (Hle : g ⊆ g'), Γ v⊢[ g' ]{ l := d } : T) ∧
  (∀ p T i, Γ v⊢ₚ[ g ] p : T, i → ∀ g' (Hle : g ⊆ g'), Γ v⊢ₚ[ g' ] p : T, i) ∧
  (∀ T1 i1 T2 i2, Γ v⊢ₜ[ g ] T1, i1 <: T2, i2 → ∀ g' (Hle : g ⊆ g'), Γ v⊢ₜ[ g' ] T1, i1 <: T2, i2).
Proof.
  eapply storeless_typing_mut_ind with
      (P := λ Γ g e T _, ∀ g' (Hle : g ⊆ g'), Γ v⊢ₜ[ g' ] e : T)
      (P0 := λ Γ g ds T _, ∀ g' (Hle : g ⊆ g'), Γ v⊢ds[ g' ] ds : T)
      (P1 := λ Γ g l d T _, ∀ g' (Hle : g ⊆ g'), Γ v⊢[ g' ]{ l := d } : T)
      (P2 := λ Γ g p T i _, ∀ g' (Hle : g ⊆ g'), Γ v⊢ₚ[ g' ] p : T, i)
      (P3 := λ Γ g T1 i1 T2 i2 _, ∀ g' (Hle : g ⊆ g'), Γ v⊢ₜ[ g' ] T1, i1 <: T2, i2);
  clear Γ g; intros;
    repeat match goal with
    | H : forall g : stys, _ |- _ => specialize (H g' Hle)
    end; eauto 3; eauto using typing_storeless.typed.
Qed.

Hint Resolve is_stamped_idsσ_ren : core.

Ltac asideLaters :=
  repeat first
    [ettrans; last (apply iSub_Later; tcrush)|
    ettrans; first (apply iLater_Sub; tcrush)].

Ltac lNext := ettrans; first apply iAnd2_Sub; tcrush.
Ltac lThis := ettrans; first apply iAnd1_Sub; tcrush.

Ltac lookup :=
  lazymatch goal with
  | |- _ v⊢ₜ[ _ ] ?T1, _ <: ?T2, _ =>
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

(*******************)
(** DERIVED RULES **)
(*******************)

Section examples_lemmas.
Context {g}.

Lemma iT_All_Ex' T2 {Γ e1 v2 T1 T3} :
  Γ v⊢ₜ[ g ] e1: TAll T1 T2 →                        Γ v⊢ₜ[ g ] tv v2 : T1 →
  T3 = T2.|[v2/] →
  (*────────────────────────────────────────────────────────────*)
  Γ v⊢ₜ[ g ] tapp e1 (tv v2) : T3.
Proof. intros; subst; by econstructor. Qed.

Lemma iT_Var' Γ x T1 T2 :
  Γ !! x = Some T1 →
  T2 = shiftN x T1 →
  (*──────────────────────*)
  Γ v⊢ₜ[ g ] tv (var_vl x) : T2.
Proof. intros; subst; tcrush. Qed.

Lemma iT_Var0 Γ T :
  Γ !! 0 = Some T →
  (*──────────────────────*)
  Γ v⊢ₜ[ g ] tv (var_vl 0) : T.
Proof. intros; eapply iT_Var'; by rewrite ?hsubst_id. Qed.

Lemma iT_Mu_E' Γ v T1 T2:
  Γ v⊢ₜ[ g ] tv v: TMu T1 →
  T2 = T1.|[v/] →
  (*──────────────────────*)
  Γ v⊢ₜ[ g ] tv v: T2.
Proof. intros; subst; auto. Qed.

Lemma Bind1 Γ T1 T2 i:
  is_stamped_ty (S (length Γ)) g T1 → is_stamped_ty (length Γ) g T2 →
  iterate TLater i T1 :: Γ v⊢ₜ[g] T1, i <: shift T2, i →
  Γ v⊢ₜ[g] μ T1, i <: T2, i.
Proof.
  intros Hus1 Hus2 Hsub.
  ettrans. exact: (iMu_Sub_Mu Hsub).
  exact: iMu_Sub.
Qed.

Lemma Bind2 Γ T1 T2 i:
  is_stamped_ty (length Γ) g T1 → is_stamped_ty (S (length Γ)) g T2 →
  iterate TLater i (shift T1) :: Γ v⊢ₜ[g] shift T1, i <: T2, i →
  Γ v⊢ₜ[g] T1, i <: μ T2, i.
Proof.
  intros Hus1 Hus2 Hsub.
  ettrans; last apply (iMu_Sub_Mu Hsub); [exact: iSub_Mu | wtcrush].
Qed.

Lemma Bind1' Γ T1 T2:
  is_stamped_ty (S (length Γ)) g T1 → is_stamped_ty (length Γ) g T2 →
  T1 :: Γ v⊢ₜ[g] T1, 0 <: shift T2, 0 →
  Γ v⊢ₜ[g] μ T1, 0 <: T2, 0.
Proof. intros; exact: Bind1. Qed.

(* Adapted from [typing_unstamped_derived.v]. *)
Lemma iP_Sub' {Γ p T1 T2 i} :
  Γ v⊢ₜ[g] T1, i <: T2, i →
  Γ v⊢ₚ[g] p : T1, i →
  Γ v⊢ₚ[g] p : T2, i.
Proof.
  intros; rewrite -(plusnO i).
  by eapply (iP_Sub 0); rewrite ?plusnO.
Qed.

Lemma iP_Sngl_Sym Γ p q i:
  is_stamped_path (length Γ) g q →
  Γ v⊢ₚ[g] p : TSing q, i →
  Γ v⊢ₚ[g] q : TSing p, i.
Proof.
  intros Hus Hpq. eapply iP_Sub'.
  eapply (iSngl_Sub_Sym Hpq). by apply iSngl_Sub_Self, Hpq.
  eapply iP_Sngl_Refl.
  by apply (iP_Sngl_Inv Hpq).
Qed.

Lemma iSngl_pq_Sub_inv {Γ i p q T1 T2}:
  T1 ~Tp[ p := q ]* T2 →
  is_stamped_ty   (length Γ) g T1 →
  is_stamped_ty   (length Γ) g T2 →
  is_stamped_path (length Γ) g p →
  Γ v⊢ₚ[g] q : TSing p, i →
  Γ v⊢ₜ[g] T1, i <: T2, i.
Proof. intros. by eapply iSngl_pq_Sub, iP_Sngl_Sym. Qed.

Lemma iP_And {Γ p T1 T2 i}:
  Γ v⊢ₚ[g] p : T1, i →
  Γ v⊢ₚ[g] p : T2, i →
  Γ v⊢ₚ[g] p : TAnd T1 T2, i.
Proof.
  intros Hp1 Hp2. eapply iP_Sub', iP_Sngl_Refl, Hp1.
  constructor; exact: iSngl_Sub_Self.
Qed.

Lemma iT_Sub_nocoerce T1 T2 {Γ e} :
  Γ v⊢ₜ[ g ] e : T1 →
  Γ v⊢ₜ[ g ] T1, 0 <: T2, 0 →
  Γ v⊢ₜ[ g ] e : T2.
Proof. intros. exact: (iT_Sub (i:=0)). Qed.
Hint Resolve iT_Sub_nocoerce : core.

Lemma iT_Var_Sub Γ x T1 T2 :
  Γ !! x = Some T1 →
  Γ v⊢ₜ[ g ] shiftN x T1, 0 <: T2, 0 →
  (*──────────────────────*)
  Γ v⊢ₜ[ g ] tv (var_vl x) : T2.
Proof. intros; eapply iT_Sub_nocoerce; by [exact: iT_Var|]. Qed.

Lemma iT_Var0_Sub Γ T1 T2 :
  Γ !! 0 = Some T1 →
  Γ v⊢ₜ[ g ] T1, 0 <: T2, 0 →
  (*──────────────────────*)
  Γ v⊢ₜ[ g ] tv (var_vl 0) : T2.
Proof. intros. by eapply iT_Var_Sub; [| rewrite ?hsubst_id]. Qed.

Lemma iSub_Sel' Γ U {p l L i}:
  is_stamped_ty (length Γ) g L →
  Γ v⊢ₚ[ g ] p : TTMem l L U, i →
  Γ v⊢ₜ[ g ] L, i <: TSel p l, i.
Proof. intros; ettrans; last exact: (iSub_Sel (p := p)); tcrush. Qed.

(** Specialization of [iSub_Sel'] for convenience. *)
Lemma iSub_Sel'' Γ {p l L i}:
  is_stamped_ty (length Γ) g L →
  Γ v⊢ₚ[ g ] p : TTMem l L L, i → Γ v⊢ₜ[ g ] L, i <: TSel p l, i.
Proof. apply iSub_Sel'. Qed.

Lemma iSub_AddIJ' {Γ T i j} (Hst: is_stamped_ty (length Γ) g T) (Hle : i <= j):
  Γ v⊢ₜ[ g ] T, i <: T, j.
Proof.
  rewrite (le_plus_minus i j Hle) Nat.add_comm; move: {j Hle} (j - i) => k.
  elim: k => [|n IHn] /=; first tcrush.
  ettrans; first apply IHn.
  ettrans; [exact: iSub_Add_Later | tcrush].
Qed.

Lemma iSub_AddI Γ T i (Hst: is_stamped_ty (length Γ) g T) :
  Γ v⊢ₜ[ g ] T, 0 <: T, i.
Proof. apply: iSub_AddIJ'; by [|lia]. Qed.

Lemma iLaterN_Sub {Γ T i j} :
  is_stamped_ty (length Γ) g T →
  Γ v⊢ₜ[g] iterate TLater j T, i <: T, j + i.
Proof.
  elim: j T => /= [|j IHj] T HuT; rewrite ?iterate_0 ?iterate_Sr /=; tcrush.
  ettrans.
  - apply (IHj (TLater T)); stcrush.
  - exact: iLater_Sub.
Qed.

Lemma path_tp_delay {Γ p T i j} (Hst: is_stamped_ty (length Γ) g T) : i <= j →
  Γ v⊢ₚ[ g ] p : T, i → Γ v⊢ₚ[ g ] p : T, j.
Proof.
  intros Hle Hp.
  rewrite (le_plus_minus i j Hle); move: {j Hle} (j - i) => k.
  eapply iP_Sub, Hp.
  apply: iSub_AddIJ'; by [|lia].
Qed.

Lemma iAnd_Later_Sub_Distr Γ T1 T2 i :
  is_stamped_ty (length Γ) g T1 →
  is_stamped_ty (length Γ) g T2 →
  Γ v⊢ₜ[ g ] TAnd (TLater T1) (TLater T2), i <: TLater (TAnd T1 T2), i.
Proof. intros; asideLaters; tcrush; [lThis|lNext]. Qed.


(* Lattice theory *)
Lemma iOr_Sub_split Γ T1 T2 U1 U2 i:
  is_stamped_ty (length Γ) g U1 →
  is_stamped_ty (length Γ) g U2 →
  Γ v⊢ₜ[ g ] T1, i <: U1, i →
  Γ v⊢ₜ[ g ] T2, i <: U2, i →
  Γ v⊢ₜ[ g ] TOr T1 T2, i <: TOr U1 U2, i.
Proof.
  intros.
  apply iOr_Sub; [
    eapply iSub_Trans, iSub_Or1 | eapply iSub_Trans, iSub_Or2]; tcrush.
Qed.

Lemma iSub_And_split Γ T1 T2 U1 U2 i:
  is_stamped_ty (length Γ) g T1 →
  is_stamped_ty (length Γ) g T2 →
  Γ v⊢ₜ[ g ] T1, i <: U1, i →
  Γ v⊢ₜ[ g ] T2, i <: U2, i →
  Γ v⊢ₜ[ g ] TAnd T1 T2, i <: TAnd U1 U2, i.
Proof.
  intros; apply iSub_And; [
    eapply iSub_Trans; first apply iAnd1_Sub |
    eapply iSub_Trans; first apply iAnd2_Sub]; tcrush.
Qed.

Lemma iAnd_Or_Sub_Distr_inv {Γ S T U i}:
  is_stamped_ty (length Γ) g S →
  is_stamped_ty (length Γ) g T →
  is_stamped_ty (length Γ) g U →
  Γ v⊢ₜ[ g ] TOr (TAnd S U) (TAnd T U), i <: TAnd (TOr S T) U , i.
Proof.
  intros; apply iOr_Sub; apply iSub_And; tcrush;
    (ettrans; first apply iAnd1_Sub); tcrush.
Qed.

Lemma iOr_And_Sub_Distr {Γ S T U i}:
  is_stamped_ty (length Γ) g S →
  is_stamped_ty (length Γ) g T →
  is_stamped_ty (length Γ) g U →
  Γ v⊢ₜ[ g ] TOr (TAnd S T) U , i <: TAnd (TOr S U) (TOr T U), i.
Proof.
  intros; apply iOr_Sub; apply iSub_And; tcrush;
    (ettrans; last apply iSub_Or1); tcrush.
Qed.

Lemma comm_and {Γ T U i} :
  is_stamped_ty (length Γ) g T →
  is_stamped_ty (length Γ) g U →
  Γ v⊢ₜ[ g ] TAnd T U, i <: TAnd U T, i.
Proof. intros; tcrush. Qed.

Lemma comm_or {Γ T U i} :
  is_stamped_ty (length Γ) g T →
  is_stamped_ty (length Γ) g U →
  Γ v⊢ₜ[ g ] TOr T U, i <: TOr U T, i.
Proof. intros; tcrush. Qed.

Lemma absorb_and_or {Γ T U i} :
  is_stamped_ty (length Γ) g T →
  is_stamped_ty (length Γ) g U →
  Γ v⊢ₜ[ g ] TAnd U (TOr T U), i <: U, i.
Proof. intros; tcrush. Qed.

Lemma absorb_or_and {Γ T U i} :
  is_stamped_ty (length Γ) g T →
  is_stamped_ty (length Γ) g U →
  Γ v⊢ₜ[ g ] TOr U (TAnd T U), i <: U, i.
Proof. intros; tcrush. Qed.

Lemma absorb_or_and2 {Γ T U i} :
  is_stamped_ty (length Γ) g T →
  is_stamped_ty (length Γ) g U →
  Γ v⊢ₜ[ g ] TOr (TAnd T U) T, i <: T, i.
Proof. intros; ettrans; first apply comm_or; tcrush. Qed.

Lemma assoc_or {Γ S T U i} :
  is_stamped_ty (length Γ) g S →
  is_stamped_ty (length Γ) g T →
  is_stamped_ty (length Γ) g U →
  Γ v⊢ₜ[ g ] TOr (TOr S T) U, i <: TOr S (TOr T U), i.
Proof. intros; tcrush; (ettrans; last apply iSub_Or2); tcrush. Qed.

Lemma assoc_and {Γ S T U i} :
  is_stamped_ty (length Γ) g S →
  is_stamped_ty (length Γ) g T →
  is_stamped_ty (length Γ) g U →
  Γ v⊢ₜ[ g ] TAnd (TAnd S T) U, i <: TAnd S (TAnd T U), i.
Proof. intros. tcrush; lThis. Qed.

(* Based on Lemma 4.3 in
https://books.google.co.uk/books?id=vVVTxeuiyvQC&lpg=PA104&pg=PA85#v=onepage&q&f=false.
Would be much easier to formalize with setoid rewriting.
*)
Lemma iOr_And_Sub_Distr_inv {Γ S T U i}:
  is_stamped_ty (length Γ) g S →
  is_stamped_ty (length Γ) g T →
  is_stamped_ty (length Γ) g U →
  Γ v⊢ₜ[ g ] TAnd (TOr S U) (TOr T U), i <: TOr (TAnd S T) U , i.
Proof.
  intros.
  ettrans; first apply iAnd_Or_Sub_Distr; stcrush => //.
  ettrans; first apply iOr_Sub_split, absorb_and_or; try apply iSub_Refl;
    stcrush => //.
  ettrans; first apply iOr_Sub_split; try apply (iSub_Refl _ _ (T := U));
    try (ettrans; first apply (comm_and (T := S))); try apply iAnd_Or_Sub_Distr; stcrush => //.
  ettrans; first apply assoc_or; stcrush => //.
  ettrans; first apply iOr_Sub_split.
  3: apply iSub_Refl; tcrush.
  3: ettrans; first apply absorb_or_and2; tcrush.
  all: tcrush.
  ettrans; first eapply comm_and; tcrush.
Qed.

(* Lemma AddIB_stp Γ T U i:
  is_stamped_ty (length Γ) g T →
  is_stamped_ty (length Γ) g U →
  Γ v⊢ₜ[ g ] T, 0 <: U, 0 →
  Γ v⊢ₜ[ g ] T, i <: U, i.
Proof.
  move => Hst Hsu Hstp; elim: i => [|n IHn]; first tcrush.
  exact: iSub_Mono.
Qed. *)

Lemma is_stamped_pvar i n : i < n → is_stamped_path n g (pv (var_vl i)).
Proof. eauto. Qed.
Lemma is_stamped_pvars i n l : i < n → is_stamped_ty n g (pv (var_vl i) @; l).
Proof. eauto using is_stamped_pvar. Qed.

Lemma iT_Let Γ t u T U :
  Γ v⊢ₜ[ g ] t : T →
  shift T :: Γ v⊢ₜ[ g ] u : shift U →
  is_stamped_ty (length Γ) g T →
  Γ v⊢ₜ[ g ] lett t u : U.
Proof. move=> Ht Hu HsT. apply /iT_All_E /Ht /iT_All_I /Hu /HsT. Qed.

(* Note how we must weaken the type (or its environment) to account for the
   self-variable of the created object. *)
Definition packTV n s := (ν {@ type "A" = (shift (idsσ n); s)}).

Lemma iD_Typ T {Γ l s σ}:
  T ~[ length Γ ] (g, (s, σ)) →
  is_stamped_σ (length Γ) g σ →
  is_stamped_ty (length Γ) g T →
  Γ v⊢[ g ]{ l := dtysem σ s } : TTMem l T T.
Proof. intros. apply (iD_Typ_Abs T); auto 3. Qed.

Lemma packTV_typed' s T n Γ :
  g !! s = Some T →
  is_stamped_ty n g T →
  n <= length Γ →
  Γ v⊢ₜ[ g ] tv (packTV n s) : typeEq "A" T.
Proof.
  move => Hlp HsT1 Hle; move: (Hle) (HsT1) => /le_n_S Hles /is_stamped_ren1_ty HsT2.
  move: (is_stamped_nclosed_ty HsT1) => Hcl.
  apply (iT_Sub_nocoerce (μ {@ typeEq "A" (shift T) }));
    last (ettrans; first apply: (iMu_Sub _ (T := {@ typeEq "A" T })); tcrush).
  apply iT_Obj_I; tcrush.
  apply (iD_Typ (shift T)); simpl; eauto 2.
  eapply extraction_inf_subst, is_stamped_ren1.
  by apply /extraction_weaken /Hle /pack_extraction.
Qed.

Lemma packTV_typed s T Γ :
  g !! s = Some T →
  is_stamped_ty (length Γ) g T →
  Γ v⊢ₜ[ g ] tv (packTV (length Γ) s) : typeEq "A" T.
Proof. intros; exact: packTV_typed'. Qed.

Lemma val_LB L U Γ i v :
  is_stamped_ty (length Γ) g L →
  is_stamped_ty (length Γ) g U →
  is_stamped_vl (length Γ) g v →
  Γ v⊢ₜ[ g ] tv v : type "A" >: L <: U →
  Γ v⊢ₜ[ g ] ▶: L, i <: (pv v @; "A"), i.
Proof.
  intros ??? Hv; apply (iSub_Sel (p := pv _) (U := U)).
  apply (path_tp_delay (i := 0)); wtcrush.
Qed.

Lemma is_stamped_sub_dm d s m n:
  is_stamped_sub n m g s →
  is_stamped_dm n g d →
  is_stamped_dm m g d.|[s].
Proof. apply is_stamped_sub_mut. Qed.

Lemma is_stamped_dtysem m n s T:
  g !! s = Some T →
  is_stamped_ty m g T →
  m ≤ n →
  is_stamped_dm n g (dtysem (idsσ m) s).
Proof.
  intros.
  by apply Trav1.trav_dtysem with (T' := T) (ts' := (m, g)), is_stamped_idsσ.
Qed.

Lemma packTV_LB s T n Γ i :
  g !! s = Some T →
  is_stamped_ty n g T →
  n <= length Γ →
  Γ v⊢ₜ[ g ] ▶: T, i <: (pv (packTV n s) @; "A"), i.
Proof.
  intros; apply /val_LB /packTV_typed'; wtcrush; cbn.
  eapply (is_stamped_sub_dm (dtysem _ _) (ren (+1))); trivial.
  exact: is_stamped_dtysem.
Qed.

Lemma val_UB L U Γ i v :
  is_stamped_ty (length Γ) g L →
  is_stamped_ty (length Γ) g U →
  is_stamped_vl (length Γ) g v →
  Γ v⊢ₜ[ g ] tv v : type "A" >: L <: U →
  Γ v⊢ₜ[ g ] (pv v @; "A"), i <: ▶: U, i.
Proof.
  intros ??? Hv; apply (iSel_Sub (p := pv _) (L := L)).
  apply (path_tp_delay (i := 0)); wtcrush.
Qed.

Lemma packTV_UB s T n Γ i :
  is_stamped_ty n g T →
  g !! s = Some T →
  n <= length Γ →
  Γ v⊢ₜ[ g ] (pv (packTV n s) @; "A"), i <: ▶: T, i.
Proof.
  intros; apply /val_UB /packTV_typed'; wtcrush.
  eapply (is_stamped_sub_dm (dtysem _ _) (ren (+1))); trivial.
  exact: is_stamped_dtysem.
Qed.

Definition tApp Γ t s :=
  lett t (lett (tv (packTV (S (length Γ)) s)) (tapp (tv x1) (tv x0))).

Lemma typeApp_typed s Γ T U V t :
  Γ v⊢ₜ[ g ] t : TAll (type "A" >: ⊥ <: ⊤) U →
  (** This subtyping premise is needed to perform "avoidance", as in compilers
    for ML and Scala: that is, producing a type [V] that does not refer to
    variables bound by let in the expression. *)
  (∀ L, typeEq "A" (shiftN 2 T) :: L :: Γ v⊢ₜ[ g ] U.|[up (ren (+1))], 0 <: shiftN 2 V, 0) →
  is_stamped_ty (length Γ) g T →
  is_stamped_ty (S (length Γ)) g U →
  g !! s = Some (shift T) →
  Γ v⊢ₜ[ g ] tApp Γ t s : V.
Proof.
  move => Ht Hsub HsT1 HsU1 Hl; move: (HsT1) => /is_stamped_ren1_ty HsT2.
  move: (HsT2) => /is_stamped_ren1_ty HsT3.
  rewrite -hrenS in HsT3.
  eapply iT_Let; [exact: Ht| |tcrush].
  eapply iT_Let; [by apply packTV_typed| |tcrush].
  rewrite /= -!hrenS -/(typeEq _ _).

  apply /iT_Sub_nocoerce /Hsub.

  eapply iT_All_Ex'; first exact: iT_Var'.
  apply: iT_Var_Sub; tcrush; rewrite /= hsubst_id //.
  rewrite !hsubst_comp; f_equal. autosubst.
Qed.

End examples_lemmas.

Hint Resolve is_stamped_pvar is_stamped_pvars iT_Sub_nocoerce : core.

Ltac var := exact: iT_Var0 || exact: iT_Var'.
Ltac varsub := (eapply iT_Var0_Sub || eapply iT_Var_Sub); first done.
Ltac mltcrush := tcrush; try ((apply Bind1' || apply Bind1); tcrush); repeat lookup.
