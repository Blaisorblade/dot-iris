(**
WIP examples constructing syntactic typing derivations.
I am also experimenting with notations, but beware the current definitions are pretty bad.
 *)
From D Require Import tactics.
From D.Dot Require Import dotsyn.
From stdpp Require Import strings.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).


(** First, let's maybe start defining some nicer notation. I have little clue what I'm doing tho.
    And this would need changing anyway if we switch to explicit labels. *)

(* Beware that "Bind Scope" just presets the scope of arguments for *new* definitions. *)

(** Notation for object values. *)
Bind Scope dms_scope with dms.
Open Scope dms_scope.
Notation " {@ } " := (@nil (string * dm)) (format "{@ }") : dms_scope.
Notation " {@ x } " := ( x :: {@} ) (format "{@  x  }"): dms_scope.
Notation " {@ x ; y ; .. ; z } " := (cons x (cons y .. (cons z nil) ..)) (format "{@  x ;  y ;  .. ;  z  }"): dms_scope.
Close Scope dms_scope.
Arguments vobj _%dms_scope.

Notation "'ν' ds " := (vobj ds) (at level 20, ds at next level).
Notation "'val' l = v" := (l, dvl v) (at level 20, l at level 10).
Notation "'type' l = ( σ ; s )" := (l, dtysem σ s) (at level 20, l at level 10).

(** Notation for object types. *)
Bind Scope ty_scope with ty.
Open Scope ty_scope.
(* Notation "⊤" := TTop : ty_scope. *)
Notation " {@ } " := TTop (format "{@ }") : ty_scope.
Notation " {@ T1 } " := ( TAnd T1 {@} ) (format "{@  T1  }"): ty_scope.
Notation " {@ T1 ; T2 ; .. ; Tn } " := (TAnd T1 (TAnd T2 .. (TAnd Tn {@})..))
                                       (format "{@  T1  ;  T2  ;  ..  ;  Tn  }") : ty_scope.
(* Notation " {@ T1 ; .. ; T2 ; Tn } " := (TAnd (TAnd .. (TAnd {@} T1) .. T2) Tn) *)
(*                                          (format "{@  T1  ;  ..  ;  T2  ;  Tn  }"): ty_scope. *)
Close Scope ty_scope.

Notation "'μ' Ts " := (TMu Ts) (at level 20, Ts at next level).
Notation "'type' l >: L <: U" := (TTMem l L U) (at level 20, l, L, U at level 10).
Notation "'val' l : T" := (TVMem l T) (at level 20, l, T at level 10).

Definition σ1 : vls := [].
Definition s1 : positive := 1.

Definition σ2 : vls := [].
Definition s2 : positive := 2.

Check ν {@ val "a" = vnat 0 }.

Check ν {@ type "A" = (σ1 ; s1) }.
Check ν {@ val "a" = vnat 0; type "A" = (σ1 ; s1) }.
Check μ {@ type "A" >: TNat <: TTop }.
Check μ {@ val "a" : TNat }.

Check vobj {@}.
Check ν {@ }.
Check ν {@ val "a" = vnat 0 }.
Check ν {@ val "a" = vnat 0 ; val "b" = vnat 1 }.
Check ν {@ val "a" = vnat 0 ; type "A" = (σ1 ; s1) }.

(* Notation "v @ l1 @ .. @ l2 ; l" := (TSel (pself .. (pself (pv v) l1) .. l2) l) *)
(*                                      (format "v  @  l1  @  ..  @  l2  ;  l", at level 69, l1, l2 at level 60). *)
(* Check (TSel (pself (pself (pv (var_vl 0)) 1) 2) 3). *)
(* Check (var_vl 0 @ 1 @ 2 ; 3). *)
Notation "v @ l1 @ .. @ l2" := (pself .. (pself (pv v) l1) .. l2)
                                     (format "v  @  l1  @  ..  @  l2", at level 69, l1, l2 at level 60).
Notation "p @; l" := (TSel p l) (at level 71).
Check (pv (var_vl 0) @; "A").
Check (pself (pself (pv (var_vl 0)) "A") "B" @; "C").
Check (var_vl 0 @ "A" @ "B" @; "C").

From D.Dot Require Import typing.

Hint Constructors typed subtype dms_typed dm_typed path_typed.

Section examples.
(* From D Require Import typeExtraction *)
Context `{hasStampTable: stampTable}.
Example ex0 e Γ T:
  Γ ⊢ₜ e : T →
  is_stamped_ty (length Γ) getStampTable T →
  Γ ⊢ₜ e : TTop.
Proof.
  intro HeT. change e with (iterate tskip 0 e).
  econstructor; first apply Top_stp; eassumption.
Qed.

(* XXX Redeclaring notation so that it picks new scopes. Once it picks new
   scopes, the pretty-printer can use overloaded notation in its arguments.
   Instead, declare scopes before typing notation. *)
Local Notation "Γ ⊢ds ds : T"  := (dms_typed Γ ds T) (at level 74, ds, T at next level).

Example ex1 Γ n T:
  Γ ⊢ₜ tv (ν {@ val "a" = vnat n}) : μ {@ val "a" : TNat }.
Proof.

  (* (* info eauto: *) *)
  (* simple eapply dcons_typed. *)
  (* simple apply dnil_typed. *)
  (* (*external*) reflexivity. *)
  (* simple apply dvl_typed. *)
  (* simple eapply Subs_typed. *)
  (* simple eapply Trans_stp. *)
  (* simple apply TSucc_stp. *)
  (* simple apply TLaterR_stp. *)
  (* simple apply Nat_typed. *)

  assert (∀ Γ, Γ ⊢ₜ TNat, 0 <: TLater TNat, 0). {
    (* eauto 3. (* Avoid longer routes.*) *)
    intro.
    eapply Trans_stp; by [apply TSucc_stp | apply TLaterR_stp].
  }
  (* Help proof search: Avoid trying TMuI_typed, that's1 slow. *)
  apply VObj_typed; first constructor; naive_solver.
Qed.

Example ex2 Γ T
  (Hs: (TSel (pv (var_vl 0)) "B") ~[ S (length Γ) ] (getStampTable, (s1, σ1))):
  Γ ⊢ₜ tv (ν {@ type "A" = (σ1 ; s1) } ) :
    TMu (TAnd (TTMem "A" TBot TTop) TTop).
Proof.
  apply VObj_typed; eauto.
  econstructor => //=.
  eapply dty_typed; eauto.
Qed.

(* Try out fixpoints. *)
Definition F3 T :=
  TMu (TAnd (TTMem "A" T T) TTop).

Example ex3 Γ T
  (Hs: (F3 (TSel (pv (var_vl 0)) "A")) ~[ S (length Γ) ] (getStampTable, (s1, σ1))):
  Γ ⊢ₜ tv (ν {@ type "A" = (σ1 ; s1) } ) :
    F3 (F3 (TSel (pv (var_vl 0)) "A")).
Proof.
  have Hst: is_stamped_ty (S (length Γ)) getStampTable (F3 (pv (var_vl 0) @; "A")).
  by constructor; naive_solver.
  apply VObj_typed; last eauto. (* Avoid trying TMuI_typed, that's slow. *)
  econstructor => //=.
  eapply dty_typed; naive_solver.
Qed.

(* Example ex3' Γ T: *)
(*   Γ ⊢ₜ tv (vobj [dtysyn (TSel (pv (var_vl 0)) 0)]) : *)
(*     F3 (F3 (TSel (pv (var_vl 0)) 0)). *)
(* Proof. *)
(*   assert (∀ T, T.|[ren (+0)] = T) as Hrew. by asimpl. *)
(*   apply VObj_typed. (* Avoid trying TMuI_typed, that's slow. *) *)
(*   econstructor => //=. *)
(*   eapply dty_typed => //=. *)
(*   econstructor => //=. *)
(* Abort. *)

Definition F4 T :=
  TMu (TAnd (TVMem "A" (TSel (pv (var_vl 0)) "B")) (TAnd (TTMem "B" T T) TTop)).
Print F4.

(* XXX Not sure I got this right. *)
Example ex4 Γ T
  (Hs: TSel (pv (var_vl 0)) "A" ~[ S (length Γ) ] (getStampTable, (s1, σ1))):
  Γ ⊢ₜ tv (ν {@ val "a" = var_vl 0; type "B" = (σ1 ; s1) }) :
    F4 (F4 (TSel (pv (var_vl 0)) "A")).
Abort.
(*     (* TMu (TAnd (TAnd TTop (TTMem 0 ?))  *) *)
(*     (*                      (TVMem 1 (TSel (pv (var_vl 0)) 0))). *) *)
(* Proof. *)
(*   assert (∀ T, T.|[ren (+0)] = T) as Hrew. by asimpl. *)
(*   apply VObj_typed. (* Avoid trying TMuI_typed, that's slow. *) *)
(*   econstructor => //=. *)
(*   { *)
(*     econstructor => //=. *)
(*     econstructor => //=. *)
(*     rewrite {3} /F4. *)
(*     - eapply Trans_stp. 2: { *)
(*         eapply LSel_stp. *)
(*         econstructor => //. *)
(*         eapply Subs_typed. 2: by apply Var_typed. *)
(*         rewrite Hrew. *)
(*         eapply Trans_stp. eapply TLaterL_stp. *)
(*         eapply Trans_stp. eapply TAnd1_stp. *)
(*         eapply Trans_stp. eapply TAnd2_stp. *)
(*         admit. *)
(*         (* econstructor => //. *) *)
(*       } *)
(*       econstructor => //=. *)
(*     - admit. *)
(*   } *)
(*   econstructor => //=. *)
(*   eapply Subs_typed. 2: by apply Var_typed. *)
(*   rewrite Hrew. *)
(*   apply TLaterCov_stp. *)
(*   eapply Trans_stp. 2: { *)
(*     eapply LSel_stp. *)
(*     econstructor =>//. *)
(*     eapply Subs_typed; last by eapply Var_typed. *)
(*     rewrite Hrew. *)
(*     eapply Trans_stp. eapply TLaterL_stp. *)
(*     eapply Trans_stp. eapply TAnd1_stp. *)
(*     eapply Trans_stp. eapply TAnd2_stp. *)
(*     admit. *)
(*     (* eapply Refl_stp. *) *)

(*   } *)
(*   rewrite /F4. *)
(*   apply TSucc_stp. *)
(*   Unshelve. *)
(*   all: eauto. *)
(* Abort. *)

End examples.
