From iris.proofmode Require Import tactics.
From D Require Export iris_prelude.
From D Require Import ty_interp_subst_lemmas lty.
From D.Dot Require Export dlang_inst path_wp.

Notation "'λI' x .. y , t" := (fun x => .. (fun y => t%I) ..)
  (at level 200, x binder, y binder, right associativity, only parsing,
  format "'[  ' '[  ' 'λI'  x  ..  y ']' ,  '/' t ']'") : function_scope.

(** Override notation from [dlang] to specify scope. *)
Notation "⟦ T ⟧" := (ty_interp T%ty).

Include TyInterpLemmas VlSorts dlang_inst.
Include LtyJudgements VlSorts dlang_inst.
(* Import SemTypes. *)

(** Deduce types from variable names, like on paper, for readability and to help
    type inference for some overloaded operations (e.g. substitution). *)
Implicit Types
         (L T U : ty) (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (vs : vls) (ρ : var → vl).

(** The logical relation core is the [interp], interprets *open* types into
    predicates over *closed* values. Hence, [interp T ρ v] uses its argument [ρ]
    to interpret anything contained in T, but not things contained in v.

    Semantic judgements must apply instead to open terms/value/paths; therefore,
    they are defined using closing substitution on arguments of [interp].

    Similar comments apply to [def_interp].

    Additionally, both apply to *translated* arguments, hence they only expect
    [dtysem] and not [dtysyn] for type member definitions.
 *)

(* Use Program without its extended pattern-matching compiler; we only need
   its handling of coercions. *)
Unset Program Cases.

Notation wf_ds ds := (NoDup (map fst ds)).

Definition path_includes p ρ ds :=
  path_wp_pure p.|[ρ] (λ w, ∃ ds', w = vobj ds' ∧ ds.|[ρ] `sublist_of` ds'.|[w/] ∧ wf_ds ds').

Definition prim_sem (B : base_ty) :=
  match B with
  | tbool => bool
  | tnat => nat
  end.

Definition prim_evals_to (B : base_ty) (v : vl) : prim_sem B → Prop :=
  match B return prim_sem B → Prop with
  | tbool => λ l, v = vlit $ lbool l
  | tnat  => λ l, v = vlit $ lnat l
  end.

Definition pure_interp_prim B v := ∃ l : prim_sem B, prim_evals_to B v l.

Record dlty Σ := Dlty {
  dlty_label : label;
  dlty_car : env -d> dm -d> iPropO Σ;
  dlty_persistent ρ d :> Persistent (dlty_car ρ d);
}.
Global Arguments Dlty {_} _%I _ {_}.
Global Arguments dlty_car {_} !_ _ _ /.
Global Arguments dlty_label {_} _ /.
Global Existing Instance dlty_persistent.

Definition lift_dlty `{!dlangG Σ} (φ : dlty Σ) l : envPred dm Σ :=
  λI ρ d, ⌜ dlty_label φ = l ⌝ ∧ dlty_car φ ρ d.

Definition dm_to_type `{!dlangG Σ} d i (ψ : hoD Σ i) : iProp Σ :=
  (∃ s σ, ⌜ d = dtysem σ s ⌝ ∧ s ↗n[ σ , i ] ψ)%I.
Notation "d ↗n[ i  ] ψ" := (dm_to_type d i ψ) (at level 20).

Section dm_to_type.
  Context `{HdotG: dlangG Σ}.

  Global Instance dm_to_type_persistent d i ψ: Persistent (d ↗n[ i ] ψ) := _.

  Lemma dm_to_type_agree d i ψ1 ψ2 args v : d ↗n[ i ] ψ1 -∗ d ↗n[ i ] ψ2 -∗ ▷ (ψ1 args v ≡ ψ2 args v).
  Proof.
    iDestruct 1 as (s σ ?) "#Hs1".
    iDestruct 1 as (s' σ' ?) "#Hs2".
    simplify_eq. by iApply (stamp_σ_to_type_agree args with "Hs1 Hs2").
  Qed.

  Lemma dm_to_type_intro d i s σ φ :
    d = dtysem σ s → s ↝n[ i ] φ -∗ d ↗n[ i ] hoEnvD_inst σ φ.
  Proof.
    iIntros. iExists s, σ. iFrame "%".
    by iApply stamp_σ_to_type_intro.
  Qed.

  Definition dm_to_type_eq d i ψ : dm_to_type d i ψ =
    (∃ s σ, ⌜ d = dtysem σ s ⌝ ∧ s ↗n[ σ , i ] ψ)%I := eq_refl.

  Global Opaque dm_to_type.
End dm_to_type.

Section SemTypes.
  Context `{HdotG: dlangG Σ}.

  Implicit Types (τ : olty Σ 0).
   (* (ψ : vl -d> iPropO Σ) (φ : envD Σ)  *)

  Program Definition lift_dinterp_vl (T : dlty Σ): olty Σ 0 :=
    olty0 (λI ρ v, (∃ d, ⌜v @ dlty_label T ↘ d⌝ ∧ dlty_car T ρ d)).

  (* Rewrite using (higher) semantic kinds! *)
  Definition oDTMem l τ1 τ2 : dlty Σ := Dlty l
    (λI ρ d,
    ∃ ψ, (d ↗n[ 0 ] ψ) ∧
       □ ((∀ v, ▷ τ1 vnil ρ v → ▷ □ ψ vnil v) ∧
          (∀ v, ▷ □ ψ vnil v → ▷ τ2 vnil ρ v))).

  Definition oTTMem l τ1 τ2 :=
    lift_dinterp_vl (oDTMem l τ1 τ2).

  Definition oDVMem l τ : dlty Σ := Dlty l
    (λI ρ d, ∃ pmem, ⌜d = dpt pmem⌝ ∧ path_wp pmem (oClose τ ρ)).

  Definition oTVMem l τ :=
    lift_dinterp_vl (oDVMem l τ).

  Definition oTSel p (l : label) :=
    olty0 (λI ρ v, path_wp p.|[ρ]
      (λ vp, ∃ ψ d, ⌜vp @ l ↘ d⌝ ∧ d ↗n[ 0 ] ψ ∧ ▷ □ ψ vnil v)).

  Lemma oTSel_pv w (l : label) args ρ v :
    oTSel (pv w) l args ρ v ⊣⊢
      ∃ ψ d, ⌜w.[ρ] @ l ↘ d⌝ ∧ d ↗n[ 0 ] ψ ∧ ▷ □ ψ vnil v.
  Proof. by rewrite /= path_wp_pv. Qed.

  Definition oPSing p : olty Σ 0 :=
    olty0 (λI ρ v, ⌜alias_paths p.|[ρ] (pv v)⌝).

  (* Paolo: This definition is contractive (similarly to what's useful for
     equi-recursive types).
     However, I am not sure we need this; it'd be good to
     write an example where this makes a difference.
     I think that would be something like
     nu x. { T = TNat; U = x.T -> x.T }:
     mu (x: {T <: TNat; U <: x.T -> TNat}).
     If the function type constructor is not contractive but only non-expansive,
     typechecking this example needs to establish x.T <: TNat having in context
     only x: {T <: TNat; U <: x.T -> TNat}.
   *)
  Definition oForall τ1 τ2 := olty0
    (λI ρ v,
    (∃ t, ⌜ v = vabs t ⌝ ∧
     □ ∀ w, ▷ τ1 vnil ρ w → ▷ interp_expr τ2 (w .: ρ) t.|[w/])).

  Definition oPrim b : olty Σ 0 := olty0 (λI ρ v, ⌜pure_interp_prim b v⌝).

  Class PersTyInterp (ty : Type) Σ :=
    pers_ty_interp : ty → olty Σ 0.
  Notation "p⟦ T ⟧" := (pers_ty_interp T%ty).
  Global Arguments pers_ty_interp {_ _ _} !_ /.

  Global Instance pinterp : PersTyInterp ty Σ :=
    fix pinterp (T : ty) : olty Σ 0 :=
    let _ := pinterp : PersTyInterp ty Σ in
    match T with
    | TTMem l L U => oTTMem l p⟦ L ⟧ p⟦ U ⟧
    | TVMem l T' => oTVMem l p⟦ T' ⟧
    | TAnd T1 T2 => oAnd p⟦ T1 ⟧ p⟦ T2 ⟧
    | TOr T1 T2 => oOr p⟦ T1 ⟧ p⟦ T2 ⟧
    | TLater T => oLater p⟦ T ⟧
    | TPrim b => oPrim b
    | TTop => oTop
    | TBot => oBot
    | TAll T1 T2 => oForall p⟦ T1 ⟧ p⟦ T2 ⟧
    | TMu T => oMu p⟦ T ⟧
    | TSel p l => oTSel p l
    | TSing p => oPSing p
    end.
  (* Wrap this into ty_interp to reuse lemmas. *)
  Global Instance pers_to_ty_interp : TyInterp ty Σ := flip pers_ty_interp vnil.
  Global Arguments pers_to_ty_interp _ /.
  Global Arguments ty_interp {_ _ _} _ /.

  Global Instance interp_lemmas: TyInterpLemmas ty Σ.
  Proof.
    split => /=; induction T => sb1 sb2 w /=;
      properness; rewrite ?scons_up_swap ?hsubst_comp; trivial; by f_equiv => ?.
  Qed.

  Global Instance interp_persistent T ρ v : Persistent (⟦ T ⟧ ρ v) := _.

  Fixpoint def_interp_base (T : ty) : dlty Σ :=
    match T with
    | TTMem l L U => oDTMem l p⟦ L ⟧ p⟦ U ⟧
    | TVMem l T' => oDVMem l p⟦ T' ⟧
    | _ => Dlty "" (λI _ _, False)
    end.

  Global Instance def_interp_persistent T ρ d :
    Persistent (dlty_car (def_interp_base T) ρ d).
  Proof. destruct T; try apply _. Qed.

  Implicit Types (l : label).

  Definition def_interp T l := lift_dlty (def_interp_base T) l.

  Definition defs_interp_and (interp1 interp2 : envPred dms Σ) : envPred dms Σ :=
    λI ρ ds, interp1 ρ ds ∧ interp2 ρ ds.

  Definition lift_dinterp_dms T : envPred dms Σ := λI ρ ds,
    ∃ l d, ⌜ dms_lookup l ds = Some d ⌝ ∧ def_interp T l ρ d.

  Fixpoint defs_interp T : envPred dms Σ :=
    match T with
    | TAnd T1 T2 => defs_interp_and (defs_interp T1) (defs_interp T2)
    | TTop => λI ρ ds, True
    | _ => lift_dinterp_dms T
    end.

  Global Instance defs_interp_persistent T ρ ds : Persistent (defs_interp T ρ ds).
  Proof. induction T; try apply _. Qed.

  (* Fixpoint interp_env (Γ : ctx) (ρ : var → vl) : iProp Σ :=
    match Γ with
    | T :: Γ' => interp_env Γ' (stail ρ) ∧ ⟦ T ⟧ ρ (shead ρ)
    | nil => True
    end%I. *)
End SemTypes.

Notation "d ↗ ψ" := (dm_to_type 0 d ψ) (at level 20).
Notation "p⟦ T ⟧" := (pers_ty_interp T%ty).
Notation "p⟦ Γ ⟧*" := (pers_ty_interp <$> Γ).
Notation "p⟦ T ⟧ₑ" := (interp_expr ⟦ T ⟧).
(* Notation "⟦ T ⟧ₑ" := (interp_expr p⟦ T ⟧). *)
(* Definition interp_env (Γ : ctx) : env -d> iPropO Σ := env_oltyped (pers_ty_interp <$> Γ).
Global Arguments interp_env !_ _ /.
Notation "⟦ Γ ⟧*" := (interp_env Γ). *)
(* Notation "⟦ Γ ⟧*" := (env_oltyped (pers_ty_interp <$> Γ)). *)
Notation "⟦ Γ ⟧*" := s⟦ p⟦ Γ ⟧* ⟧*.

(* Definition idtp `{!dlangG Σ} Γ l (φ : dlty Σ) d : iProp Σ :=
  (⌜ dlty_label φ = l ⌝ ∧
    □∀ ρ, ⟦Γ⟧* ρ → dlty_car φ ρ d.|[ρ])%I. *)
Definition idtp `{!dlangG Σ} Γ l (φ : dlty Σ) d : iProp Σ :=
  □∀ ρ, ⌜path_includes (pv (ids 0)) ρ [(l, d)] ⌝ → s⟦Γ⟧* ρ → lift_dlty φ l ρ d.|[ρ].
Global Arguments idtp /.
Notation "Γ s⊨ { l := d  } : T" := (idtp Γ l T d) (at level 74, d, l, T at next level).

Definition idstp `{!dlangG Σ} Γ T ds : iProp Σ :=
  ⌜wf_ds ds⌝ ∧ □∀ ρ, ⌜path_includes (pv (ids 0)) ρ ds ⌝ → s⟦Γ⟧* ρ → defs_interp T ρ ds.|[ρ].
Global Arguments idstp /.
(** Multi-definition typing *)
Notation "Γ s⊨ds ds : T" := (idstp Γ T ds) (at level 74, ds, T at next level).

Definition iptp `{!dlangG Σ} Γ (τ : olty Σ 0) p i: iProp Σ :=
  □∀ ρ, ⟦Γ⟧* ρ -∗
    ▷^i path_wp (p.|[ρ]) (λ v, oClose τ ρ v).
Global Arguments iptp /.
Notation "Γ s⊨p p : τ , i" := (iptp Γ τ p i) (at level 74, p, τ, i at next level).

(** Single-definition typing *)
Notation "Γ ⊨ {  l := d  } : T" := (idtp p⟦Γ⟧* p⟦T⟧ l d) (at level 74, d, l, T at next level).
(** Multi-definition typing *)
Notation "Γ ⊨ds ds : T" := (idstp p⟦Γ⟧* p⟦T⟧ ds) (at level 74, ds, T at next level).
(** Expression typing *)
Notation "Γ ⊨ e : T" := (ietp p⟦Γ⟧* p⟦T⟧ e) (at level 74, e, T at next level).
Notation "Γ ⊨p p : T , i" := (iptp p⟦Γ⟧* p⟦T⟧ p i) (at level 74, p, T, i at next level).

Notation "Γ ⊨ T1 , i <: T2 , j " := (step_indexed_ivstp p⟦Γ⟧* p⟦T1⟧ p⟦T2⟧ i j) (at level 74, T1, T2, i, j at next level).

Import stamp_transfer.
(** Single-definition typing *)
Notation "Γ ⊨[ gφ  ] { l := d  } : T" := (wellMappedφ gφ → Γ ⊨ {  l := d  } : T)%I (at level 74, d, l, T at next level).
(** Multi-definition typing *)
Notation "Γ ⊨ds[ gφ  ] ds : T" := (wellMappedφ gφ → Γ ⊨ds ds : T)%I (at level 74, ds, T at next level).
(** Expression typing *)
Notation "Γ ⊨[ gφ  ] e : T" := (wellMappedφ gφ → Γ ⊨ e : T)%I (at level 74, e, T at next level).
Notation "Γ ⊨p[ gφ  ] p : T , i" := (wellMappedφ gφ → Γ ⊨p p : T , i)%I (at level 74, p, T, i at next level).
Notation "Γ ⊨[ gφ  ] T1 , i <: T2 , j" := (wellMappedφ gφ → Γ ⊨ T1 , i <: T2 , j)%I (at level 74, T1, T2, i, j at next level).

Section logrel_lemmas.
  Context `{!dlangG Σ}.

  Lemma iterate_TLater_later0 i T ρ v:
    oClose (p⟦ iterate TLater i T ⟧) ρ v ≡ oClose (olty0 (λI ρ v, ▷^i p⟦ T ⟧ vnil ρ v)) ρ v.
  Proof. elim: i => [|i IHi] //. rewrite iterate_S /= IHi //. Qed.

  (* Lemma iterate_TLater_later i T ρ v:
    ⟦ iterate TLater i T ⟧ ρ v ≡ (▷^i ⟦ T ⟧ ρ v)%I.
  Proof. exact: iterate_TLater_later0. Qed. *)

  Lemma def_interp_tvmem_eq l T p ρ:
    def_interp (TVMem l T) l ρ (dpt p) ⊣⊢
    path_wp p (⟦ T ⟧ ρ).
  Proof.
    iSplit. by iDestruct 1 as (_ pmem [= ->]) "$".
    iIntros "H"; iSplit; first done; iExists p. by auto.
  Qed.

  Lemma interp_env_lookup' Γ ρ T x:
    Γ !! x = Some T →
    ⟦ Γ ⟧* ρ -∗ ⟦ (shiftN x T) ⟧ ρ (ρ x).
  Proof.
    elim: Γ ρ x => [//|τ' Γ' IHΓ] ρ x Hx /=.
    iDestruct 1 as "[Hg Hv]". move: x Hx => [ [->] | x Hx] /=.
    - rewrite hsubst_id. by [].
    - rewrite hrenS.
      iApply (interp_weaken_one (shiftN x T)).
      iApply (IHΓ (stail ρ) x Hx with "Hg").
  Qed.

  Lemma sSub_Refl Γ (T : olty Σ 0) i : Γ s⊨ T, i <: T, i.
  Proof. by iIntros "!> **". Qed.

  Lemma sSub_Trans Γ (T1 T2 T3 : olty Σ 0) i1 i2 i3 :
    Γ s⊨ T1, i1 <: T2, i2 -∗
    Γ s⊨ T2, i2 <: T3, i3 -∗
    Γ s⊨ T1, i1 <: T3, i3.
  Proof.
    iIntros "#Hsub1 #Hsub2 !> * #Hg #HT /=".
    iApply ("Hsub2" with "[//] (Hsub1 [//] [//])").
  Qed.

  (* Context {Γ : sCtx Σ}. *)
  Context {Γ : ctx}.
  Implicit Type (τ : olty Σ 0).

  Lemma Sub_Refl T i : Γ ⊨ T, i <: T, i.
  Proof. apply sSub_Refl. Qed.

  Lemma Sub_Trans T1 T2 T3 i1 i2 i3 : Γ ⊨ T1, i1 <: T2, i2 -∗
                                      Γ ⊨ T2, i2 <: T3, i3 -∗
                                      Γ ⊨ T1, i1 <: T3, i3.
  Proof. apply sSub_Trans. Qed.

  Lemma Sub_Eq T U i j :
    Γ ⊨ T, i <: U, j ⊣⊢
    Γ ⊨ iterate TLater i T, 0 <: iterate TLater j U, 0.
  Proof. by cbn; setoid_rewrite iterate_TLater_later0. Qed.
End logrel_lemmas.

From D Require Import swap_later_impl.
Import dlang_adequacy adequacy.

Theorem s_adequacy_dot_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} e Ψ
  (τ : ∀ `{dlangG Σ}, olty Σ 0)
  (Himpl : ∀ (Hdlang: dlangG Σ) v, oClose τ ids v -∗ ⌜Ψ v⌝)
  (Hlog : ∀ `{dlangG Σ} `(!SwapPropI Σ), allGs ∅ ==∗ [] s⊨ e : τ):
  ∀ σ, adequate NotStuck e σ (λ v _, Ψ v).
Proof.
  eapply (adequacy_dlang _); [apply Himpl | iIntros (??) "Hgs"].
  iMod (Hlog with "Hgs") as "#Htyp".
  iEval rewrite -(hsubst_id e). iApply ("Htyp" $! ids with "[//]").
Qed.

Theorem adequacy_dot_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} e Ψ T
  (Himpl : ∀ (Hdlang: dlangG Σ) v, ⟦ T ⟧ ids v -∗ ⌜Ψ v⌝)
  (Hlog : ∀ `{dlangG Σ} `(!SwapPropI Σ), allGs ∅ ==∗ [] ⊨ e : T):
  ∀ σ, adequate NotStuck e σ (λ v _, Ψ v).
Proof. exact: (s_adequacy_dot_sem Σ e Ψ (λ _, p⟦T⟧)). Qed.

Corollary s_safety_dot_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} e
  (τ : ∀ `{dlangG Σ}, olty Σ 0)
  (Hwp : ∀ `{dlangG Σ} `(!SwapPropI Σ), allGs ∅ ==∗ [] s⊨ e : τ):
  safe e.
Proof. apply adequate_safe, (s_adequacy_dot_sem _ e _ τ), Hwp; naive_solver. Qed.

Corollary safety_dot_sem Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} e T
  (Hwp : ∀ `{dlangG Σ} `(!SwapPropI Σ), allGs ∅ ==∗ [] ⊨ e : T):
  safe e.
Proof. exact: (s_safety_dot_sem Σ e (λ _, p⟦T⟧)). Qed.
