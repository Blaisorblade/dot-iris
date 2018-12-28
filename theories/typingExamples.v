From Dot Require Import tactics dotsyn typing.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Hint Constructors typed subtype dms_typed dm_typed path_typed.

Example ex0 e Γ T:
  Γ ⊢ₜ e : T →
  Γ ⊢ₜ e : TTop.
Proof.
  (* eauto 2. *)
  econstructor. apply Top_stp. eassumption.
Qed.

Example ex1 Γ n T:
  Γ ⊢ₜ tv (vobj [dvl (vnat n)]) : TMu (TAnd TTop (TVMem 0 TNat)).
Proof.
  (* Help proof search: *)
  apply VObj_typed. (* Avoid trying TMuI_typed, that's slow. *)

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
  naive_solver.
Qed.

Example ex2 Γ T:
  Γ ⊢ₜ tv (vobj [dtysyn (TSel (pv (var_vl 0)) 0)]) :
    TMu (TAnd TTop (TTMem 0 TBot TTop)).
Proof.
  apply VObj_typed.
  econstructor => //=.
  econstructor => //=.
Qed.

(* Try out fixpoints. *)
Definition F3 T :=
  TMu (TAnd TTop (TTMem 0 T T)).

Example ex3 Γ T:
  Γ ⊢ₜ tv (vobj [dtysyn (F3 (TSel (pv (var_vl 0)) 0))]) :
    F3 (F3 (TSel (pv (var_vl 0)) 0)).
Proof.
  apply VObj_typed. (* Avoid trying TMuI_typed, that's slow. *)
  econstructor => //=.
  eapply dty_typed; trivial.
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

(* Definition F4 T := *)
(*   TMu (TAnd (TAnd TTop (TTMem 0 T T))  *)
(*             (TVMem 1 (TSel (pv (var_vl 0)) 0))). *)

(* Example ex3 Γ T: *)
(*   Γ ⊢ₜ tv (vobj [dvl (var_vl 0); *)
(*                    dtysyn (TSel (pv (var_vl 0)) 0)]) : *)
(*     F4 (F4 (TSel (pv (var_vl 0)) 0)). *)
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
