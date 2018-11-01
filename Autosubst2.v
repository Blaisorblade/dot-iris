(** * Autosubst 2
    Common Definitions and Notations used by generated code.
    Note: This is still work in progress. *)
Require Import Coq.Arith.Plus Coq.Lists.List.
Set Implicit Arguments.

Definition index := nat.
Definition ren := index -> index.

Definition idren {A} (x : A) := x.
Arguments idren {A} x /.
Hint Unfold id.

Delimit Scope subst_scope with subst.
Open Scope subst_scope.

(** Forward function composition *)

Definition funcomp {A B C : Type} (f : A -> B) (g : B -> C) x := g (f x).
Arguments funcomp {A B C} f g x /.

Notation "f >>> g" := (funcomp f g)
  (at level 56, left associativity) : subst_scope.

(** Stream cons *)

Definition scons {X} (x : X) (xi : index -> X) (n : index) :=
  match n with
  | 0 => x
  | S n => xi n
  end.
Notation "x .: xr" := (scons x xr)
  (at level 55, xr at level 56, right associativity) : subst_scope.

Goal forall X (x: X) sigma n,
  (S >>> scons x sigma) n = sigma n. 
Proof.
  intros X x sigma n. destruct n. reflexivity. reflexivity.
Qed.


Definition up_ren (xi : ren) : ren :=
  0 .: xi >>> S.
 
Definition ap {X Y} (f : X -> Y) {x y : X} (p : x = y) : f x = f y :=
  match p with eq_refl => eq_refl end.

Definition apc {X Y} {f g : X -> Y} {x y : X} (p : f = g) (q : x = y) : f x = g y :=
  match q with eq_refl => match p with eq_refl => eq_refl end end.


Definition up_ren_ren (xi1 xi2 xi3 : ren) (E : forall n,  (xi1 >>> xi2) n = xi3 n) :
  forall n, (up_ren xi1 >>> up_ren xi2) n = up_ren xi3 n :=
  fun x => match x with O => eq_refl | S y => ap S (E y) end.


Fixpoint ren_of (As : list Type) : Type :=
  match As with
  | nil => unit
  | cons A nil => index -> index
  | cons A Bs => (index -> index) * ren_of Bs
  end.



(** Addition with different simplification behavior *)

Definition lift (x y : index) : index := plus x y.
Arguments lift x y/.
Notation "( + x )" := (lift x) (format "( + x )") : subst_scope.

(** ** Canonical Structures for Substitutions

  I remember reading that depending on the implementation, unification in Coq
  proceeds from left-to-right or from right-to-left. The function inst takes
  an unecessary argument of type X to trigger unification from both directions,
  since this is needed to typecheck the substitution.

  TODO: Check this. *)

Fixpoint subst_of (As : list Type) : Type :=
  match As with
  | nil => unit
  | cons A Ar =>
    match Ar with
    | nil => index -> A
    | cons B Br => (index -> A) * subst_of Ar
    end
  end.

Structure substMixin (X : Type) := {
  subst_of_substType : list Type;
  inst_of_substType :
    subst_of subst_of_substType -> X -> X
}.

Structure substType := Pack {
  subst_ofType :> Type;
  mixin_of_substType :> substMixin subst_ofType;
  _ : Type
}.

Definition inst {X : substType} (s : X) (sigma : subst_of (subst_of_substType X)) (_ : X) : X :=
  inst_of_substType X sigma s.

Notation "s .[ sigma ]" := (inst s sigma s)
  (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]" ) : subst_scope.

Definition comp {X : substType} (sigma : index -> X) (taus : subst_of (subst_of_substType X))
  (_ : index -> X) : index -> X := fun x => (sigma x).[taus].

Notation "sigma >> taus" := (comp sigma taus sigma)
  (at level 56, left associativity) : subst_scope.

Fixpoint eq_of_subst {As : list Type} : subst_of As -> subst_of As -> Prop :=
  match As with
  | nil => fun _ _ => True
  | cons A Ar =>
    match Ar as Ar return
          (subst_of Ar -> subst_of Ar -> Prop) ->
          subst_of (A :: Ar) -> subst_of (A :: Ar) -> Prop with
    | nil => fun _ sigma tau => forall i, sigma i = tau i
    | cons B Br => fun eqn sigmas taus =>
      match sigmas, taus with
      | (sigma, sigmar), (tau, taur) =>
        (forall i, sigma i = tau i) /\ eqn sigmar taur
      end
    end (@eq_of_subst Ar)
  end.

Definition substEq {X : substType} (sigma tau : subst_of (subst_of_substType X)) : Prop :=
  eq_of_subst sigma tau.
(* Notation "sigmas == taus" := (substEq sigmas taus) (at level 50) : subst_scope.

Lemma eq_of_subst_refl {As : list Type} (sigmas : subst_of As) :
  eq_of_subst sigmas sigmas.
Proof.
  revert sigmas. induction As. cbn. auto. destruct As. cbn. intros i. reflexivity.
  intros [sigma sigmar]. split. intros i. reflexivity. apply IHAs.
Qed.

Lemma eq_of_subst_sym {As : list Type} (sigmas taus : subst_of As) :
  eq_of_subst sigmas taus -> eq_of_subst taus sigmas.
Proof.
  revert sigmas taus. induction As. auto. destruct As. cbn. eauto.
  intros [sigma sigmar] [tau taur] [e1 e2]. split. eauto.
  now apply IHAs.
Qed.

Lemma eq_of_subst_trans {As : list Type} (sigmas taus thetas : subst_of As) :
  eq_of_subst sigmas taus -> eq_of_subst taus thetas -> eq_of_subst sigmas thetas.
Proof.
  revert sigmas taus thetas. induction As. auto.
  destruct As. cbn; intros ??? e1 e2 i. now rewrite e1.
  intros [sigma sigmar] [tau taur] [theta thetar] [e1l e1r] [e2l e2r]. split.
  intros i. now rewrite e1l. apply (IHAs _ _ _ e1r e2r).
Qed.

Lemma substEq_refl {X : substType} (sigmas : subst_of (subst_of_substType X)) :
  sigmas == sigmas.
Proof. apply eq_of_subst_refl. Qed.

Lemma substEq_sym {X : substType} (sigmas taus : subst_of (subst_of_substType X)) :
  taus == sigmas -> sigmas == taus.
Proof. apply eq_of_subst_sym. Qed.

Lemma substEq_trans {X : substType} (sigmas taus thetas : subst_of (subst_of_substType X)) :
  sigmas == taus -> taus == thetas -> sigmas == thetas.
Proof. apply eq_of_subst_trans. Qed. *)

(** ** Asimpl

  The "asimpl" tactic simplifies substitution expressions everywhere in the goal.
  We use the type class Asimpl to track which terms are substitution expressions
  and how to normalize them. An instance for [Asimpl x y] marks [x] as a substitution
  expression with normal form [y]. The top level asimpl tactic replaces
  terms by their normal forms everywhere in the goal.

  ---
  Implementation notes:

  The implementation of asimpl is not entirely straightforward, because we have to
  take care to generate small proof terms (simulating the sigma-calculus results in
  many rewrite steps and large proof terms lead to terrible performance), and we
  should never call type class inference after replacing a term by its normal form.

  For the first point, we check convertibility and only generate proof terms
  for equations when we cannot simply use conversion.
  The second point means that we cannot simply use ltac's context match, but rather
  that we have to implement this ourselves.
 *)

Class Asimpl {X : Type} (x y : X) := asimplEqn : x = y.
Hint Mode Asimpl + + - : typeclass_instances.

Class Funext := funext : forall (A : Type) (B : A -> Type) (f g : forall x, B x),
   (forall x, f x = g x) -> f = g.

(** [has_funext]
   Succeeds if a [Funext] instance is present in the contexts, fails otherwise. *)
Ltac has_funext :=
  let FE := constr:(ltac:(once (typeclasses eauto)) : Funext) in idtac.

Ltac asimpl_typeclass_inference x :=
  constr:(ltac:(once (typeclasses eauto)) : Asimpl x _).
  
(** [asimpl_in_context x ce cc]

  Runs asimpl on the term [x], returns its result by calling the ice/icc continuations.
  Let [y] be the normal form of [x]. If [x] and [y] are convertible, [asimpl_in_context]
  calls the [cc] continuation with [y]. Otherwise, it calls the [ce] continuation with
  a context [p] and a proof of an equation [eqn]. The context is an ltac function from
  terms to terms represented as tactics. Let [eqn : a = b], then [x] is convertible to
  [p a], and [y] is convertible to [p b]. *)
Ltac asimpl_in_context ix ice icc :=
  let rec in_context x ce cc :=
    first [
      (* try to simplify x at top level *)
      (let eqn := asimpl_typeclass_inference x in
       lazymatch type of eqn with
       | Asimpl _ ?y =>
         (*idtac "simplify" x "to" y;*)
         first [
           (* if x and y are convertible, call the cc continuation with the normal form *)
           unify x y; cc y |
           (* otherwise call the ce continuation with an empty context and the proof of x = y *)
           let ctx xt := exact xt in
           let eqn' := eval unfold Asimpl in eqn in
           ce ctx (eqn' : x = y)]
       end) |
      (* we couldn't simplify x, so we recurse *)
      lazymatch x with
      | (?f ?a) =>
        lazymatch type of f with
        (* if f has a simple type, we recurse into both f and a *)
        | ?NN -> ?MM =>
          let in_context_feqn p e :=
           (let in_context_ap2 q e' :=
              (*idtac "in_context_ap2";*)
              let ctx xt := exact xt in
              let u := fresh in
              let v := fresh in
              let eqn := constr:(f_equal2 (fun u v => ltac:(p u) ltac:(q v)) e e') in
              ce ctx eqn in
            let in_context_apL a' :=
              (*idtac "in_context_apL";*)
              let ctx xt := exact (ltac:(p xt) a') in
              ce ctx e in
            in_context a in_context_ap2 in_context_apL) in
          let in_context_fconv f' :=
           (let in_context_apR p e :=
              (*idtac "in_context_apR";*)
              let ctx xt := exact (f' ltac:(p xt)) in
              ce ctx e in
            let in_context_ap0 a' :=
              (*idtac "in_context_ap0";*)
              cc (f' a') in
            in_context a in_context_apR in_context_ap0) in
          in_context f in_context_feqn in_context_fconv
        (* if f is dependently typed, we only recurse into f *)
        | _ =>
          let in_context_apD p e :=
              (*idtac "in_context_apD";*)
              let ctx xt := exact (ltac:(p xt) a) in
              ce ctx e in
          let in_context_ap1 f' :=
              (*idtac "in_context_apD0";*)
              cc (f' a) in
          in_context f in_context_apD in_context_ap1
        end
      (* non-dependent products *)
      | ?A -> ?B =>
        let in_context_aeqn p e :=
            let in_context_arr2 q e' :=
              let ctx xt := exact xt in
              let u := fresh in
              let v := fresh in
              let eqn := constr:(f_equal2 (fun u v => ltac:(p u) -> ltac:(q v)) e e') in
              ce ctx eqn in
            let in_context_arrL B' :=
                let ctx xt := exact (ltac:(p xt) -> B') in
                ce ctx e in
            in_context B in_context_arr2 in_context_arrL in
        let in_context_aconv A' :=
            let in_context_arrR p e :=
                let ctx xt := exact (A' -> ltac:(p xt)) in
                ce ctx e in
            let in_context_arr0 B' :=
                cc (A' -> B') in
            in_context B in_context_arrR in_context_arr0 in
        in_context A in_context_aeqn in_context_aconv
      (* x is some term which we can't simplify *)
      | _ => (*idtac "in_context_id";*) cc x
      end ]
  in in_context ix ice icc.

Ltac asimpl :=
  let A := match goal with |- ?A => constr:(A) end in
  let rewrite_in_goal p e :=
      (*idtac "rewrite_in_goal";*)
      let U := match type of e with @eq ?U _ _ => U end in
      let B := fresh in
      let ctx := constr:(fun (B : U) => ltac:(p B)) in
      refine (@eq_rect_r U _ ctx _ _ e) in
  let change_goal B :=
      (*idtac "change_goal" B;*)
      (change B) in
  asimpl_in_context A rewrite_in_goal change_goal.

Ltac autosubst := asimpl; now trivial.

(** ** Recursive Simplification

    Computing the normal form of a substitution expression may require computing
    the normal forms of arbitrary subterms. The class [AsimplRec] can be used
    to invoke asimpl on arbitrary terms during type class inference. *)

Class AsimplRec {X : Type} (x y : X) := asimplRecEqn : x = y.
Hint Mode AsimplRec + + - : typeclass_instances.

Ltac asimpl_eqn x :=
  let to_equation p e :=
      (*idtac "to_equation";*)
      let U := match type of e with @eq ?U _ _ => U end in
      let B := fresh in
      let ctx := constr:(fun (B : U) => ltac:(p B)) in
      refine (@f_equal U _ ctx _ _ e) in
  let to_eq_refl y :=
      (*idtac "to_eq_refl" y;*)
      exact (eq_refl y) in
  asimpl_in_context x to_equation to_eq_refl.

Hint Extern 1 (AsimplRec ?x _) => asimpl_eqn x.

(** ** Reflection Helpers (from Krebbers' std++ library) *)

Section quote_lookup.
  Context {A : Type}.
  Class QuoteLookup (E1 E2 : list A) (x : A) (i : nat) := {}.
  Global Instance quote_lookup_here E x : QuoteLookup (x :: E) (x :: E) x 0.
  Global Instance quote_lookup_end x : QuoteLookup nil (cons x nil) x 0.
  Global Instance quote_lookup_further E1 E2 x i y :
    QuoteLookup E1 E2 x i -> QuoteLookup (y :: E1) (y :: E2) x (S i) | 1000.
End quote_lookup.
Hint Mode QuoteLookup + + - + - : typeclass_instances.

(** ** Simplifying Index Expressions *)
(* This is more of a proof of concept for using reflection in asimpl.
   In an ideal world asimpl would always use reflection to simplify
   substitution expressions, but let's see how feasible that is in practice...*)

Module AsimplIndex.
  (** *** Normalizing Reflected Terms *)

  Inductive exp :=
  | EO
  | ES (s : exp)
  | EVar (i : nat)
  | EPlus (s t : exp).

  Definition nf : Type := nat * list nat.

  Fixpoint eval_exp (E : list index) (s : exp) : index :=
    match s with
    | EO => 0
    | ES s => S (eval_exp E s)
    | EVar n => nth n E 0
    | EPlus s t => (eval_exp E s) + (eval_exp E t)
    end.

  Fixpoint flatten (E : list index) (xs : list nat) : index :=
    match xs with
    | nil => 0
    | cons n nil => nth n E 0
    | cons n xr => flatten E xr + nth n E 0
    end.

  Definition eval_nf (E : list index) (s : nf) : index :=
    match s with
    | (n, nil) => n
    | (0, xs) => flatten E xs
    | (n, xs) => n + flatten E xs
    end.

  Fixpoint normalize (s : exp) : nf :=
    match s with
    | EO => (0,nil)
    | ES s => match normalize s with (k, xs) => (S k, xs) end
    | EVar i => (0, cons i nil)
    | EPlus s t =>
      match normalize s, normalize t with
      | (m, xs), (n, ys) => (m+n, ys ++ xs)
      end
    end.

  Lemma eval_nfE (E : list index) n xs :
    eval_nf E (n,xs) = n + flatten E xs.
  Proof.
    destruct n, xs; cbn; eauto.
  Qed.

  Lemma flatten_cat (E : list index) (xs ys : list nat) :
    flatten E ys + flatten E xs = flatten E (xs ++ ys).
  Proof.
    induction xs; cbn; eauto. destruct xs.
    - cbn. destruct ys; cbn; trivial.
    - rewrite plus_assoc, IHxs; trivial.
  Qed.

  Lemma normalize_sound (E : list index) (s : exp) :
    eval_exp E s = eval_nf E (normalize s).
  Proof.
    induction s; cbn.
    - trivial.
    - rewrite IHs. destruct (normalize s). rewrite !eval_nfE. trivial.
    - trivial.
    - rewrite IHs1, IHs2. destruct (normalize s1), (normalize s2).
      rewrite !eval_nfE. rewrite <- plus_assoc, (plus_comm (flatten E l)).
      rewrite !plus_assoc. rewrite <- plus_assoc, (plus_comm (flatten _ _)).
      rewrite flatten_cat. reflexivity.
  Qed.

  (** *** Reifying Index Expressions *)

  Class ReifyExp (Ein Eout : list index) (s : index) (e : exp) := {}.
  Hint Mode ReifyExp + - ! - : typeclass_instances.

  Instance ReifyO (E : list index) : ReifyExp E E 0 EO.
  Instance ReifyS (Ein Eout : list index) (s : index) (e : exp) (r : ReifyExp Ein Eout s e) :
    ReifyExp Ein Eout (S s) (ES e).

  Instance ReifyPlus (E1 E2 E3 : list index) (s t : index) (e1 e2 : exp)
           (r1 : ReifyExp E1 E2 s e1) (r2 : ReifyExp E2 E3 t e2) :
    ReifyExp E1 E3 (s + t) (EPlus e1 e2).

  Instance ReifyVar (E1 E2 : list index) (s : index) i :
    QuoteLookup E1 E2 s i -> ReifyExp E1 E2 s (EVar i) | 100.

  (** *** Reflection tactic *)
  Ltac asimpl_index x :=
    lazymatch type of (_ : ReifyExp nil _ x _) with
    (* prevent loops *)
    | ReifyExp _ _ _ (EVar 0) => fail
    (* Recursively simplify *)
    | ReifyExp _ ?E _ ?e =>
      let eqn := constr:(ltac:(asimpl_eqn E)) in
      lazymatch type of eqn with
      | _ = ?E' =>
          let nf := eval vm_compute in (normalize e) in
          let z := eval compute[eval_nf flatten nth] in (eval_nf E' nf) in
          exact (@eq_trans index x (eval_nf E (normalize e)) z
                   (@normalize_sound E e)
                   (@f_equal (list index) index (fun E'' => eval_nf E'' nf) E E' eqn))
      end
    end.
End AsimplIndex.

(** *** Integration with asimpl *)
Class AsimplIndex (x y : index) := asimplIndexEqn : x = y.
Hint Extern 1 (AsimplIndex ?x _) => AsimplIndex.asimpl_index x : typeclass_instances.
Hint Mode AsimplIndex + - : typeclass_instances.

Instance AsimplIndexRefl x :
  AsimplIndex x x | 100.
Proof. reflexivity. Qed.


(** ** Simplifying Renamings *) 

Class AsimplRen (xi1 xi2 : ren) := asimplRenEqn : forall x, xi1 x = xi2 x.
Hint Mode AsimplRen + - : typeclass_instances.

(** *** Simplify shift *)

Class AsimplRenShift (x : index) (xi : ren) :=
  asimplRenShiftEqn : forall i, (+x) i = xi i.
Hint Mode AsimplRenShift + - : typeclass_instances.

Instance AsimplRenShiftIdren : AsimplRenShift 0 id.
Proof. hnf; auto. Qed.

Instance AsimplRenShiftDef (x : index) : AsimplRenShift x (+x) | 100.
Proof. hnf; auto. Qed.

Instance AsimplRenSShift {x y : index} {xi : ren}
  (E1 : AsimplIndex x y) (E2 : AsimplRenShift y xi) : AsimplRen (+x) xi.
Proof. rewrite E1. apply E2. Qed.

(** *** Simplify scons *) 
Class AsimplRenCons (x : index) (xi zeta : ren) :=
  asimplRenConsEqn : forall i, (x .: xi) i = zeta i.
Hint Mode AsimplRenCons + + - : typeclass_instances.

Instance AsimplRenConsEta {n : nat} {x : index} {xi zeta : ren} :
  AsimplRenCons (zeta n) ((+S n) >>> zeta) ((+n) >>> zeta).
Proof.
  intros [|i]; cbn. now rewrite <- plus_n_O. now rewrite <- plus_n_Sm.
Qed.

Instance AsimplRenConsDef {x : index} {xi : ren} :
  AsimplRenCons x xi (x .: xi) | 100.
Proof. intros i. reflexivity. Qed.

Instance AsimplRenScons {x y : index} {xi1 xi2 zeta : ren}
  (E1 : AsimplIndex x y) (E2 : AsimplRen xi1 xi2) (E3 : AsimplRenCons y xi2 zeta) :
  AsimplRen (x .: xi1) zeta.
Proof.
  intros i. rewrite <- E3. destruct i; eauto.
Qed.

(** *** Simplify composition *)

Class AsimplRenComp (xi1 xi2 zeta : ren) := asimplRenCompEqn : forall i, (xi1 >>> xi2) i = zeta i.
Hint Mode AsimplRenComp + + - : typeclasses_eauto.

Instance AsimplRenCompIdL {xi : ren} : AsimplRenComp idren xi xi.
Proof. hnf; eauto. Qed.

Instance AsimplRenCompIdR {xi : ren} : AsimplRenComp xi idren xi.
Proof. hnf; eauto. Qed.

Instance AsimplRenCompComp {xi1 xi2 xi3 zeta zeta': ren}
  (E : AsimplRenComp xi2 xi3 zeta) (E': AsimplRenComp xi1 zeta zeta'): AsimplRenComp (xi1 >>> xi2) xi3 zeta'.
Proof. intros i. rewrite <- E'. simpl in *. apply E. Qed. 

Instance AsimplRenCompShift {n : nat} {x : index} {xi zeta : ren}
  (E : AsimplRenComp (+n) xi zeta) : AsimplRenComp (+S n) (x .: xi) zeta.
Proof. intros i. apply E. Qed.

(* redundant terms pop up because of the rule above *)
Instance AsimplRenCompShift0 {xi : ren} : AsimplRenComp (+0) xi xi.
Proof. hnf; auto. Qed.

Class AsimplRenInst (x : index) (xi : ren) (y : index) := asimplRenInstEqn : xi x = y.
Hint Mode AsimplRenInst + + - : typeclass_instances.

Instance AsimplRenCompCons {x y : index} {xi1 xi2 zeta : ren}
  (E1 : AsimplRenInst x xi2 y) (E2 : AsimplRenComp xi1 xi2 zeta) :
  AsimplRenComp (x .: xi1) xi2 (y .: zeta).
Proof. intros [|i]; cbn. apply E1. apply E2. Qed.

Instance AsimplRenInstShift {x y z : index}
  (E : AsimplIndex (y + x) z) : AsimplRenInst x (+y) z.
Proof. apply E. Qed.
 
Instance AsimplRenInstShiftComp {x y z u : index} {xi : ren}
  (E1 : AsimplIndex (y + x) z) (E2 : AsimplRenInst z xi u) : AsimplRenInst x ((+y) >>> xi) u.
Proof. hnf. cbn. rewrite E1. apply E2. Qed.

Instance AsimplRenInstCons0 {x : index} {xi : ren} : AsimplRenInst 0 (x .: xi) x.
Proof. reflexivity. Qed.

Instance AsimplRenInstConsS {x y z : index} {xi : ren}
  (E : AsimplRenInst x xi z) : AsimplRenInst (S x) (y .: xi) z.
Proof. apply E. Qed.

Instance AsimplRenInstIdren {x : index} : AsimplRenInst x idren x.
Proof. reflexivity. Qed.

Instance AsimplRenInstRefl {x : index} {xi : ren} : AsimplRenInst x xi (xi x) | 100.
Proof. reflexivity. Qed.

Instance AsimplRenCompRefl {xi1 xi2 : ren} : AsimplRenComp xi1 xi2 (xi1 >>> xi2) | 100.
Proof. intros i. reflexivity. Qed.

(** *** Everything else is an opaque term *)

Instance AsimplRenRefl {xi : ren} : AsimplRen xi xi | 100.
Proof. hnf; auto. Qed.


(** ** Simplifying Substitutions *)
Class AsimplComp {A B C} (sigma: A -> B) (tau: B -> C) zeta := asimplCompEqn : forall i, (sigma >>> tau) i = zeta i.
Hint Mode AsimplComp + + + + + - : typeclass_instances. 

Class AsimplCons {X} (s: X) (sigma tau: index -> X) := asimplConsEqn : forall x, (s.: sigma) x = tau x.
Hint Mode AsimplCons + + + - : typeclass_instances. 

Class AsimplGen {X} (sigma tau : index -> X) := asimplGenEqn : forall x, sigma x = tau x.
Hint Mode AsimplGen + + - : typeclass_instances. 

Class AsimplVarInst {X} (x : index) (sigma : index -> X) s := asimplVarInstEqn : sigma x = s.
Hint Mode AsimplVarInst + + + - : typeclass_instances.

(** ** AsimplCons *)
Instance AsimplConsRefl {X} (sigma : index -> X) (s : X) :
  AsimplCons s sigma (s .: sigma)  | 100.
Proof.
  intros x; reflexivity. 
Qed.

Instance AsimplConsEta {X} (sigma: index -> X) :
  AsimplCons (sigma 0) (S >>> sigma) sigma.
Proof.
  intros x. destruct x; reflexivity.
Qed.


(** ** AsimplVar *)
Instance AsimplVarInstShiftComp X {x y z : index} u {sigma : index -> X}
  (E1 : AsimplIndex (y + x) z) (E2 : AsimplVarInst z sigma u) : AsimplVarInst x ((+y) >>> sigma) u.
Proof. hnf. cbn. rewrite E1. apply E2. Qed.

Instance AsimplVarInstCons0 X s {sigma: index -> X} : AsimplVarInst 0 (s .: sigma) s.
Proof. reflexivity. Qed.

Instance AsimplVarInstConsS X {x : index} s t {sigma : index -> X}
  (E : AsimplVarInst x sigma s) : AsimplVarInst (S x) (t .: sigma) s.
Proof. apply E. Qed.
 
Instance AsimplVarInstRefl X {x : index} {sigma : index -> X} : AsimplVarInst x sigma (sigma x) | 100.
Proof. reflexivity. Qed.


(** *** Composition *)
Instance AsimplCompRefl A B C (sigma: A -> B) (tau: B -> C) :
  AsimplComp sigma tau (sigma >>> tau) | 100.
Proof. intros x. reflexivity. Qed. 

Instance AsimplCompAsso A B C D (sigma: B -> C) (tau: C -> D) sigma_tau (zeta : A -> B) zeta' (E: AsimplComp sigma tau sigma_tau) (E': AsimplComp zeta sigma_tau zeta'):
  AsimplComp (zeta >>> sigma) tau zeta'. 
Proof. intros x. rewrite <- E'. simpl. apply E. Qed.

(** **** Composition with cons *)

(* USE AsimplInst!? *)
Instance AsimplCompConsL X Y (s: X) (s': Y) sigma tau zeta zeta' (E: Asimpl (tau s) s') (E'': AsimplComp sigma tau zeta) (E': AsimplCons s' zeta zeta')  :
  AsimplComp (s.: sigma) tau zeta'.
Proof. intros x. rewrite <- E', <- E. destruct x.
reflexivity. simpl. apply E''. 
Qed. 

Instance AsimplCompS' X (s: X) sigma :
  AsimplComp (+1) (s.:sigma) sigma.
Proof.
  intros x. reflexivity. 
Qed. 

Instance AsimplCompIdL X Y (sigma: X -> Y):
  AsimplComp sigma id sigma.
Proof. intros x. reflexivity. Qed.

Instance AsimplCompIdR X Y (sigma: X -> Y):
  AsimplComp id sigma sigma.
Proof. intros x. reflexivity. Qed.


(* AsimplGen *)

Instance AsimplGenRefl X (sigma : index -> X) :
  AsimplGen sigma sigma | 100.
Proof. intros x. reflexivity. Qed. 

Instance AsimplGenCons X (s t: X) sigma tau zeta (E_s: Asimpl s t) (E: AsimplGen sigma tau) (E': AsimplCons t tau zeta) :
  AsimplGen (s.: sigma) zeta.
Proof. intros x. rewrite <- E'. rewrite E_s. destruct x; simpl; congruence. 
Qed. 

Instance AsimplGenRen X (xi xi': index -> index) (sigma tau theta: index -> X) (E: AsimplRen xi xi') (E': AsimplGen sigma tau) (E'' : AsimplComp xi' tau theta) :
  AsimplGen (xi >>> sigma) theta.
Proof.
  intros x. simpl. rewrite E, E'. apply E''. 
Qed. 

(** **** Composition with shift *)

(** *** Composition with renamings *)

Class AsimplSubstCompRen {X} (xi : ren) (sigma tau : index -> X) :=
  asimplSubstCompRenEqn : forall i, (xi >>> sigma) i = tau i.
Hint Mode AsimplSubstCompRen + + + - : typeclass_instances.

Instance AsimplSubstCompRenAssoc {X} {xi1 xi2 zeta : ren} {sigma : index -> X}
  (E : AsimplRenComp xi1 xi2 zeta) : AsimplSubstCompRen xi1 (xi2 >>> sigma) (zeta >>> sigma).
Proof. intros i. cbn. f_equal. apply E. Qed.

Instance AsimplSubstCompRenRefl {X} {xi : ren} {sigma : index -> X} :
  AsimplSubstCompRen xi sigma (xi >>> sigma) | 100.
Proof. intros i. reflexivity. Qed.

(** *** Application with general functions *)

Class AsimplGenInst A (x : index) (xi : index -> A) (y : A) := asimplGenInstEqn : xi x = y.
Hint Mode AsimplGenInst + + + - : typeclass_instances.

Instance AsimplGenInstShift {x y z : index}
  (E : AsimplIndex (y + x) z) : AsimplGenInst x (+y) z.
Proof. apply E. Qed.
 
Instance AsimplGenInstShiftComp {A} {x y z : index} {xi : index -> A} {u : A}
  (E1 : AsimplIndex (y + x) z) (E2 : AsimplGenInst z xi u) : AsimplGenInst x ((+y) >>> xi) u.
Proof. hnf. cbn. rewrite E1. apply E2. Qed.

Instance AsimplGenInstCons0 {A} {x : A} {xi : index -> A} : AsimplGenInst 0 (x .: xi) x.
Proof. reflexivity. Qed.

Instance AsimplGenInstConsS {A} {x : index} {y z : A} {xi : index -> A}
  (E : AsimplGenInst x xi z) : AsimplGenInst (S x) (y .: xi) z.
Proof. apply E. Qed.

Instance AsimplGenInstIdren {x : index} : AsimplGenInst x idren x.
Proof. reflexivity. Qed.

Instance AsimplGenInstRefl {A} {x : index} {xi : index -> A} : AsimplGenInst x xi (xi x) | 100.
Proof. reflexivity. Qed.

Typeclasses Opaque funcomp.
Typeclasses Opaque scons.

Instance AsimplGen_Asimpl (X: Type) (sigma sigma': index -> X) (x : index) (y : X)
  (E1: AsimplGen sigma sigma') (E2 : AsimplGenInst x sigma' y) :
  Asimpl (sigma x) y | 95.
Proof.
  hnf. rewrite E1. apply E2.
Qed.

(** **** Asimpl with funext *)

Instance AsimplGen_Asimpl_Ext {X : Type} {H : Funext} (sigma tau : index -> X) (E : AsimplGen sigma tau) :
  Asimpl sigma tau.
Proof. apply funext. exact E. Qed.

Notation "f == g" := (forall x, f x = g x) (at level 70).
