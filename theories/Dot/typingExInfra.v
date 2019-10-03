(**
Infrastructure for typing examples.
*)
From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

(****************)
(** NOTATIONS  **)
(****************)

(** First, let's maybe start defining some nicer notation. I have little clue what I'm doing tho.
    *)

(* Beware that "Bind Scope" just presets the scope of arguments for *new* definitions. *)

(** Notation for object values. *)

Open Scope dms_scope.
Notation " {@ } " := (@nil (string * dm)) (format "{@ }") : dms_scope.
Notation " {@ x } " := ( x :: {@} ) (format "{@  x  }"): dms_scope.
Notation " {@ x ; y ; .. ; z } " :=
  (cons x (cons y .. (cons z nil) ..))
  (* (format "{@  x ;  y ;  .. ;  z  }") *)
  (format "'[v' {@  '[' x ']' ;  '/' y ;  '/' .. ;  '/' z } ']'")
  : dms_scope.

Close Scope dms_scope.
Arguments vobj _%dms_scope.

Notation "'ν' ds " := (vobj ds) (at level 60, ds at next level).
Notation "'val' l = v" := (l, dvl v) (at level 60, l at level 50).
Notation "'type' l = ( σ ; s )" := (l, dtysem σ s) (at level 60, l at level 50).

(** Notation for object types. *)
Open Scope ty_scope.
Notation "⊤" := TTop : ty_scope.
Notation "⊥" := TBot : ty_scope.
(* Notation " {@ } " := TTop (format "{@ }") : ty_scope. *)
Notation " {@ T1 } " := ( TAnd T1 ⊤ ) (format "{@  T1  }"): ty_scope.
Notation " {@ T1 ; T2 ; .. ; Tn } " :=
  (TAnd T1 (TAnd T2 .. (TAnd Tn ⊤)..))
  (* (format "'[v' {@  '[' T1 ']'  ;   T2  ;   ..  ;   Tn } ']'") : ty_scope. *)
  (format "'[v' {@  '[' T1 ']'  ;  '/' T2  ;  '/' ..  ;  '/' Tn } ']'") : ty_scope.
(* Notation " {@ T1 ; .. ; T2 ; Tn } " := (TAnd (TAnd .. (TAnd {@} T1) .. T2) Tn) *)
(*                                          (format "{@  T1  ;  ..  ;  T2  ;  Tn  }"): ty_scope. *)
Close Scope ty_scope.
Delimit Scope ty_scope with ty.

Check {@ TNat ; TNat ; TNat } % ty.

Notation "'ℕ'" := TNat  (only parsing) : ty_scope.
Notation "'𝐍'" := TNat : ty_scope.

Notation "'▶'" := TLater : ty_scope.
(* Level taken from Iris. *)
Notation "'▶' T" := (TLater T) (at level 20, right associativity) : ty_scope.

(* Do not use, too many conflicts. *)
Notation "'∀' T ',' U" := (TAll T U) (at level 49, only printing) : ty_scope.
(* Notation "'∀' '(' T ')' U" := (TAll T U) (at level 60). *)
(* Notation "'∀' '(' T ')' U" := (TAll T U)
  (at level 30, format "'∀'  '(' T ')'   U") : ty_scope. *)

Notation "'μ' Ts " := (TMu Ts) (at level 50, Ts at next level).
Notation "'type' l >: L <: U" := (TTMem l L U) (at level 60, l at level 50, L, U at level 70) : ty_scope.
Notation "'val' l : T" :=
  (TVMem l T)
  (at level 60, l, T at level 50, format "'[' 'val'  l  :  T  ']' '/'") : ty_scope.

Notation σ1 := ([] : vls).
Notation s1 := (1 % positive).

Notation σ2 := ([] : vls).
Notation s2 := (2 % positive).

Check ν {@ val "a" = vnat 0 }.

Check ν {@ type "A" = (σ1 ; s1) }.
Check ν {@ val "a" = vnat 0; type "A" = (σ1 ; s1) }.
Check μ {@ type "A" >: TNat <: TTop }.
Check μ {@ val "a" : TNat }.
Check μ {@ type "A" >: TNat <: TTop ; val "a" : TNat ; val "b" : TNat }.

Check vobj {@}.
Check ν {@ }.
Check ν {@ val "a" = vnat 0 }.
Check ν {@ val "a" = vnat 0 ; val "b" = vnat 1 }.
Check ν {@ val "a" = vnat 0 ; type "A" = (σ1 ; s1) }.

(* Notation "v @ l1 @ .. @ l2 ; l" := (TSel (pself .. (pself (pv v) l1) .. l2) l) *)
(*                                      (format "v  @  l1  @  ..  @  l2  ;  l", at level 69, l1, l2 at level 60). *)
(* Check (TSel (pself (pself p0 1) 2) 3). *)
(* Check (x0 @ 1 @ 2 ; 3). *)

Notation "v @ l1 @ .. @ l2" := (pself .. (pself (pv v) l1) .. l2)
                                     (format "v  @  l1  @  ..  @  l2", at level 69, l1, l2 at level 60).

Notation "p @; l" := (TSel p l) (at level 69).
Notation x0 := (var_vl 0).
Notation x1 := (var_vl 1).
Notation x2 := (var_vl 2).
Notation x3 := (var_vl 3).
Notation x4 := (var_vl 4).
Notation x5 := (var_vl 5).
Notation p0 := (pv x0).
Notation p1 := (pv x1).
Notation p2 := (pv x2).
Notation p3 := (pv x3).
Notation p4 := (pv x4).
Notation p5 := (pv x5).

Check (p0 @; "A").
Check (pself (pself p0 "A") "B" @; "C").
Check (x0 @ "A").
Check (x0 @ "A" @ "B" @; "C").

Notation TUnit := (⊤ % ty : ty).
Notation tUnit := (tv (vnat 0) : tm).

(***************)
(** WEAKENING **)
(***************)
From D.Dot Require Export typing.
From D.Dot Require Import traversals stampedness typeExtractionSyn.

Lemma extr_dtysem_stamped {g s} σ T n :
  T ~[ n ] (g, (s, σ)) →
  valid_stamp g σ s.
Proof. intros Hst. by rewrite /= /extraction in Hst |- *; ev; eauto 3. Qed.

Lemma extraction_weaken m n T gsσ :
  T ~[ n ] gsσ → n <= m → T ~[ m ] gsσ.
Proof.
  move: gsσ => [g [s σ]] /= [T' ?] Hle; ev.
  exists T'; split_and!; eauto using nclosed_σ_mono.
Qed.

(* While other lemmas allow to produce a suitable stamp table, for examples it makes more sense to have a generic one. *)
Lemma pack_extraction g s T n σ :
  g !! s = Some T →
  nclosed T n →
  σ = idsσ n →
  T ~[ n ] (g, (s, σ)).
Proof. move => Hcl Hl ->; exists T. by rewrite length_idsσ closed_subst_idsρ. Qed.

(****************)
(** AUTOMATION **)
(****************)
(* Prevent simplification from unfolding it, basically unconditionally. *)
Arguments extraction : simpl never.

Hint Extern 5 (nclosed _ _) => by solve_fv_congruence : fvc.
Hint Resolve pack_extraction : fvc.
Ltac by_extcrush := by auto with fvc.

(* For performance, keep these hints local to examples *)
Hint Extern 5 => try_once extraction_weaken.
Hint Extern 5 (is_stamped_ty _ _ _) => try_once is_stamped_weaken_ty.

(* Deterministic crush. *)
Ltac dcrush := repeat constructor.
Ltac by_dcrush := by dcrush.

Import Trav1.

Ltac stconstructor := match goal with
  | |- forall_traversal_tm   _ _ _ => constructor
  | |- forall_traversal_vl   _ _ _ => constructor
  | |- forall_traversal_dm   _ _ _ => constructor
  | |- forall_traversal_path _ _ _ => constructor
  | |- forall_traversal_ty   _ _ _ => constructor
  | |- Forall _ _ => constructor
  end.
Ltac typconstructor := match goal with
  | |- typed _ _ _ => constructor
  | |- dms_typed _ _ _ _ => constructor
  | |- dm_typed _ _ _ _ _ => constructor
  | |- path_typed _ _ _ _ => constructor
  | |- subtype _ _ _ _ _ => constructor
  end.
Ltac stcrush := try ((progress repeat stconstructor); eauto).
(** [tcrush] is the safest automation around. *)
Ltac tcrush := repeat typconstructor; stcrush; try solve [ done |
  try_once extraction_weaken; eauto |
  try_once is_stamped_weaken_ty; eauto ].

Hint Extern 10 (_ ≤ _) => lia : core.

Hint Constructors typed subtype dms_typed dm_typed path_typed.
Remove Hints Trans_stp.
Hint Extern 10 => try_once Trans_stp.

Hint Extern 5 => try_once is_stamped_mono_ty.
Hint Extern 0 (dms_hasnt _ _) => done.

Hint Immediate Nat.lt_0_succ.

Definition typeEq l T := (type l >: T <: T) % ty.

(********************)
(** BINDING LEMMAS **)
(********************)

Lemma scompA a b c : a >> b >> c = a >> (b >> c).
Proof. by rewrite /scomp/= -!subst_compX. Qed.

Lemma ren_ren_comp i j : ren (+i) >> ren (+j) = ren (+j + i).
Proof. autosubst. Qed.

Lemma ren_upn_gen i j k : ren (+i + j) >> upn i (ren (+k)) = ren (+i + j + k).
Proof.
  induction k. rewrite up_id_n; autosubst.
  replace (i + j + S k) with (S (i + j + k)) by lia.
  rewrite (renS_comp (i + j + k)) -IHk -ren_ren_comp.
  rewrite !(scompA _ _ (upn _ _)) !up_liftn.
  autosubst.
Qed.

Lemma hren_upn_gen i j k T : T.|[ren (+i + j)].|[upn i (ren (+k))] = T.|[ren (+i + j + k)].
Proof. by rewrite !hsubst_comp ren_upn_gen. Qed.

Lemma hren_upn i T : T.|[ren (+i)].|[upn i (ren (+1))] = T.|[ren (+S i)].
Proof.
  move: (ren_upn_gen i 0 1). by rewrite plusnS !plusnO hsubst_comp =>->.
Qed.

(*******************)
(** DERIVED RULES **)
(*******************)

Section examples_lemmas.
(* From D Require Import typeExtraction *)
Context `{hasStampTable: stampTable}.

Lemma Appv_typed' T2 {Γ e1 v2 T1 T3} :
  Γ ⊢ₜ e1: TAll T1 T2 →                        Γ ⊢ₜ tv v2 : T1 →
  T3 = T2.|[v2/] →
  (*────────────────────────────────────────────────────────────*)
  Γ ⊢ₜ tapp e1 (tv v2) : T3.
Proof. intros; subst; by econstructor. Qed.

Lemma Var_typed' Γ x T1 T2 :
  Γ !! x = Some T1 →
  T2 = T1.|[ren (+x)] →
  (*──────────────────────*)
  Γ ⊢ₜ tv (var_vl x) : T2.
Proof. intros; subst; tcrush. Qed.

Lemma TMuE_typed' Γ v T1 T2:
  Γ ⊢ₜ tv v: TMu T1 →
  T2 = T1.|[v/] →
  (*──────────────────────*)
  Γ ⊢ₜ tv v: T2.
Proof. intros; subst; auto. Qed.

Lemma Subs_typed_nocoerce T1 T2 {Γ e} :
  Γ ⊢ₜ e : T1 →
  Γ ⊢ₜ T1, 0 <: T2, 0 →
  Γ ⊢ₜ e : T2.
Proof. rewrite -(iterate_0 tskip e). eauto. Qed.
Hint Resolve Subs_typed_nocoerce.

Lemma Var_typed_sub Γ x T1 T2 :
  Γ !! x = Some T1 →
  Γ ⊢ₜ T1.|[ren (+x)], 0 <: T2, 0 →
  (*──────────────────────*)
  Γ ⊢ₜ tv (var_vl x) : T2.
Proof. intros; eapply Subs_typed_nocoerce; by [exact: Var_typed|]. Qed.

Lemma LSel_stp' Γ U {p l L i}:
  (is_stamped_ty (length Γ) getStampTable) L →
  Γ ⊢ₚ p : TTMem l L U, i →
  Γ ⊢ₜ L, i <: TSel p l, i.
Proof.
  intros.
  eapply Trans_stp; last exact: (LSel_stp _ p).
  induction (plength p); rewrite /= ?iterate_0 ?iterate_S; tcrush.
  eapply Trans_stp; first exact: TAddLater_stp; tcrush.
Qed.

Lemma AddI_stp Γ T i (Hst: (is_stamped_ty (length Γ) getStampTable) T) :
  Γ ⊢ₜ T, 0 <: T, i.
Proof.
  elim: i => [|n IHn]; first tcrush.
  eapply Trans_stp; first apply IHn.
  eapply Trans_stp; [exact: TAddLater_stp | tcrush].
Qed.

Lemma AddIB_stp Γ T U i:
  Γ ⊢ₜ T, 0 <: U, 0 →
  Γ ⊢ₜ T, i <: U, i.
Proof.
  move => Hstp; elim: i => [|n IHn]; first tcrush.
  exact: TMono_stp.
Qed.

Lemma is_stamped_pvar i n : i < n → is_stamped_path n getStampTable (pv (var_vl i)).
Proof. eauto. Qed.
Lemma is_stamped_pvars i n l : i < n → is_stamped_ty n getStampTable (pv (var_vl i) @; l).
Proof. eauto using is_stamped_pvar. Qed.

Definition vabs' x := tv (vabs x).
Definition lett t u := tapp (vabs' u) t.
Lemma Let_typed Γ t u T U :
  Γ ⊢ₜ t : T →
  T.|[ren (+1)] :: Γ ⊢ₜ u : U.|[ren (+1)] →
  (is_stamped_ty (length Γ) getStampTable) T →
  Γ ⊢ₜ lett t u : U.
Proof. move=> Ht Hu HsT. apply /App_typed /Ht /Lam_typed /Hu /HsT. Qed.

Lemma is_stamped_ren1_ty i T g:
  is_stamped_ty i g T ->
  is_stamped_ty (S i) g (T.|[ren (+1)]).
Proof. apply is_stamped_sub_ty, is_stamped_ren_shift; lia. Qed.

Definition packTV n s := (ν {@ type "A" = (idsσ (S n); s)}).

Lemma packTV_typed s T Γ :
  is_stamped_ty (length Γ) getStampTable T →
  getStampTable !! s = Some T.|[ren (+1)] →
  Γ ⊢ₜ tv (packTV (length Γ) s) : (typeEq "A" T).
Proof.
  move => HsT1.
  move: (HsT1) (HsT1) => /is_stamped_ren1_ty HsT2 /is_stamped_nclosed_ty Hcl Hlp.
  apply (Subs_typed_nocoerce (μ {@ typeEq "A" T.|[ren (+1)] })).
  - apply VObj_typed; tcrush.
    eapply (dty_typed T.|[ren (+1)]); cbn; tcrush; last exact: is_stamped_idsσ_ren.
    apply pack_extraction => //. eapply nclosed_sub_app, Hcl; auto.
  - eapply Trans_stp; first apply (Mu_stp _ ({@ typeEq "A" T })); tcrush.
Qed.

Definition tApp Γ t s :=
  lett t (lett (tv (packTV (S (length Γ)) s)) (tapp (tv x1) (tv x0))).

Lemma typeApp_typed s Γ T U V t :
  Γ ⊢ₜ t : TAll (type "A" >: ⊥ <: ⊤) U →
  (** This subtyping premise is needed to perform "avoidance", as in compilers
    for ML and Scala: that is, producing a type [V] that does not refer to
    variables bound by let in the expression. *)
  (∀ L, typeEq "A" T.|[ren (+2)] :: L :: Γ ⊢ₜ U.|[up (ren (+1))], 0 <: V.|[ren (+2)], 0) →
  is_stamped_ty (length Γ) getStampTable T →
  is_stamped_ty (S (length Γ)) getStampTable U →
  getStampTable !! s = Some T.|[ren (+2)] →
  Γ ⊢ₜ tApp Γ t s : V.
Proof.
  move => Ht Hsub HsT1 HsU1 Hl; move: (HsT1) => /is_stamped_ren1_ty HsT2.
  move: (HsT2) => /is_stamped_ren1_ty HsT3.
  rewrite -hrenS in HsT3; rewrite hrenS in Hl.
  eapply Let_typed; [exact: Ht| |tcrush].
  eapply Let_typed; [by apply packTV_typed, Hl| |tcrush].
  rewrite /= -!hrenS -/(typeEq _ _).

  apply /Subs_typed_nocoerce /Hsub.

  eapply Appv_typed'; first exact: Var_typed'.
  apply: Var_typed_sub; repeat tcrush; rewrite /= hsubst_id //.
  rewrite !hsubst_comp; f_equal. autosubst.
Qed.

(* Testcase. *)
Definition IFTBody := (TAll (p0 @; "A") (TAll (p1 @; "A") (p2 @; "A"))).
Definition IFT : ty :=
  TAll (type "A" >: ⊥ <: ⊤) IFTBody.

Lemma subIFT i Γ T:
  is_stamped_ty (length Γ) getStampTable T.|[ren (+i)] →
  (typeEq "A" T.|[ren (+1+i)]) :: Γ ⊢ₜ IFTBody, 0 <:
    TAll T.|[ren (+1+i)] (TAll T.|[ren (+2+i)] (▶ T.|[ren (+3+i)])), 0.
Proof.
  rewrite /= -/IFTBody => HsT1.
  move: (HsT1) => /is_stamped_ren1_ty HsT2; rewrite -hrenS in HsT2.
  move: (HsT2) => /is_stamped_ren1_ty HsT3; rewrite -hrenS in HsT3.
  tcrush; rewrite ?iterate_S ?iterate_0 /=;
    first [apply: LSel_stp' | apply: SelU_stp]; tcrush; apply: Var_typed';
    rewrite ?hsubst_id //; by [| autosubst].
Qed.

Lemma tAppIFT_typed Γ T t s :
  is_stamped_ty (length Γ) getStampTable T →
  getStampTable !! s = Some T.|[ren (+2)] →
  Γ ⊢ₜ t : IFT →
  Γ ⊢ₜ tApp Γ t s :
    TAll T (TAll T.|[ren (+1)] (▶ T.|[ren (+2)])).
Proof.
  move => HsT1 Hl Ht; move: (HsT1) => /is_stamped_ren1_ty HsT2.
  intros; eapply typeApp_typed => //; tcrush.
  intros; asimpl. exact: (subIFT 1).
Qed.

Definition iftCoerce t :=
  lett t (vabs' (vabs' (tskip (tapp (tapp (tv x2) (tv x1)) (tv x0))))).

Lemma coerce_tAppIFT Γ t T :
  is_stamped_ty (length Γ) getStampTable T →
  Γ ⊢ₜ t : TAll T (TAll T.|[ren (+1)] (▶ T.|[ren (+2)])) →
  Γ ⊢ₜ iftCoerce t : TAll T (TAll T.|[ren (+1)] T.|[ren (+2)]).
Proof.
  move => HsT1 Ht.
  move: (HsT1) => /is_stamped_ren1_ty HsT2.
  move: (HsT2) => /is_stamped_ren1_ty; rewrite -hrenS => HsT3.
  move: (HsT3) => /is_stamped_ren1_ty; rewrite -hrenS => HsT4.
  eapply Let_typed; [exact: Ht| |tcrush].
  rewrite /= !(hren_upn_gen 1) (hren_upn_gen 2) /=.
  tcrush; rewrite -!hrenS -(iterate_S tskip 0).
  eapply (Subs_typed _ _ (▶T.|[_])); first tcrush.
  eapply App_typed; last exact: Var_typed';
    eapply App_typed; last exact: Var_typed'.
  apply: Var_typed' => //.
  rewrite /= !(hren_upn 1) (hren_upn_gen 1) (hren_upn_gen 2)
    !hsubst_comp !ren_ren_comp /=. done.
Qed.

Lemma tAppIFT_coerced_typed Γ T t s :
  is_stamped_ty (length Γ) getStampTable T →
  getStampTable !! s = Some T.|[ren (+2)] →
  Γ ⊢ₜ t : IFT →
  Γ ⊢ₜ iftCoerce (tApp Γ t s) :
    TAll T (TAll T.|[ren (+1)] T.|[ren (+2)]).
Proof. intros. by apply /coerce_tAppIFT /tAppIFT_typed. Qed.

Definition p0Bool := (p0 @; "Boolean").
Lemma p0BoolStamped: is_stamped_ty 1 getStampTable p0Bool.
Proof. tcrush. Qed.
Hint Resolve p0BoolStamped.

Lemma IFTStamped: is_stamped_ty 0 getStampTable IFT.
Proof. tcrush. Qed.
Hint Resolve IFTStamped.

Lemma tAppIFT_coerced_typed_IFT Γ t s :
  getStampTable !! s = Some IFT →
  Γ ⊢ₜ t : IFT →
  Γ ⊢ₜ iftCoerce (tApp Γ t s) :
    TAll IFT (TAll IFT IFT).
Proof. intros. apply tAppIFT_coerced_typed; eauto 2. Qed.

Hint Extern 5 (is_stamped_ty _ _ _) => cbn.
Definition IFTp0 := TAll p0Bool (TAll p0Bool.|[ren (+1)] (p0Bool.|[ren (+2)])).

Lemma tAppIFT_coerced_typed_p0Boolean Γ T t s :
  getStampTable !! s = Some p0Bool.|[ren (+2)] →
  T :: Γ ⊢ₜ t : IFT →
  T :: Γ ⊢ₜ iftCoerce (tApp (T :: Γ) t s) :
    TAll p0Bool (TAll p0Bool.|[ren (+1)] p0Bool.|[ren (+2)]).
Proof. intros. apply tAppIFT_coerced_typed; eauto 3. Qed.

Definition iftTrue := vabs (vabs' (vabs' (tv x1))).
Definition iftFalse := vabs (vabs' (vabs' (tv x0))).

Example iftTrueTyp Γ : Γ ⊢ₜ tv iftTrue : IFT.
Proof. tcrush. exact: Var_typed'. Qed.
Example iftFalseTyp Γ : Γ ⊢ₜ tv iftFalse : IFT.
Proof. tcrush. exact: Var_typed'. Qed.

Definition iftNot Γ t s :=
  tapp (tapp
      (iftCoerce (tApp Γ t s))
    (tv iftFalse))
  (tv iftTrue).

Lemma iftNotTyp Γ T t s :
  getStampTable !! s = Some IFT →
  Γ ⊢ₜ t : IFT →
  Γ ⊢ₜ iftNot Γ t s : IFT.
Proof.
  intros.
  eapply App_typed; last exact: iftTrueTyp.
  eapply App_typed; last exact: iftFalseTyp.
  exact: tAppIFT_coerced_typed_IFT.
Qed.

Definition iftAnd Γ t1 t2 s :=
  tapp (tapp
      (iftCoerce (tApp Γ t1 s))
    t2)
  (tv iftFalse).

Lemma iftAndTyp Γ T t1 t2 s :
  getStampTable !! s = Some IFT →
  Γ ⊢ₜ t1 : IFT →
  Γ ⊢ₜ t2 : IFT →
  Γ ⊢ₜ iftAnd Γ t1 t2 s : IFT.
Proof.
  intros Hs Ht1 Ht2.
  eapply App_typed; last exact: iftFalseTyp.
  eapply App_typed; last exact: Ht2.
  exact: tAppIFT_coerced_typed_IFT.
Qed.

End examples_lemmas.

Hint Resolve is_stamped_pvar is_stamped_pvars Subs_typed_nocoerce.
