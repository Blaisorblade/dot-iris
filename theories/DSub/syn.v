From D.DSub Require Export dsub_syn.

(** After instantiating Autosubst, a few binding-related syntactic definitions
    that need not their own file. *)

(** Here is a manual proof of a lemma, with explanations. *)
Lemma fv_vabs_inv_manual e n: nclosed_vl (vabs e) n → nclosed e (S n).
Proof.
  rewrite /nclosed_vl /nclosed => /= Hfv s1 s2 HsEq.

  (** From Hfv, we only learn that [e.|[up s1] = e.|[up s2]], for arbitrary [s1]
      and [s2], but substitutions in our thesis [e.|[s1] = e.|[s2]] are not of form [up ?].
      Hence, we rewrite it using [decomp_s] / [decomp_s_vl] to get a
      substitution of form [up ?], then rewrite with [e.|[up (stail s1)] =
      e.|[up (stail s2)]] (got from [Hfv]), and conclude.
      *)
  rewrite ?(decomp_s _ s1) ?(decomp_s _ s2) ?(decomp_s_vl _ s1) ?(decomp_s_vl _ s2) (eq_n_s_heads HsEq); last lia.
  injection (Hfv _ _ (eq_n_s_tails HsEq)); rewritePremises; reflexivity.
Qed.

Section syntax_mut_ind_closed.
  Variable Ptm : tm → nat → Prop.
  Variable Pvl : vl → nat → Prop.
  Variable Pty : ty → nat → Prop.

  Implicit Types (n: nat).

  Variable step_tv : ∀ n v1,
      nclosed_vl v1 n → nclosed (tv v1) n → Pvl v1 n → Ptm (tv v1) n.
  Variable step_tapp : ∀ n t1 t2,
      nclosed t1 n → nclosed t2 n → nclosed (tapp t1 t2) n →
      Ptm t1 n → Ptm t2 n → Ptm (tapp t1 t2) n.
  Variable step_tskip : ∀ n t1,
      nclosed t1 n → nclosed (tskip t1) n →
      Ptm t1 n → Ptm (tskip t1) n.
  Variable step_var_vl : ∀ n i,
      nclosed_vl (var_vl i) n → Pvl (var_vl i) n.
  Variable step_vnat : ∀ n m,
      nclosed_vl (vnat m) n → Pvl (vnat m) n.
  Variable step_vabs : ∀ n t1,
      nclosed t1 (S n) →
      nclosed_vl (vabs t1) n →
      Ptm t1 (S n) → Pvl (vabs t1) n.

  Variable step_vty : ∀ n T1,
      nclosed T1 n → nclosed_vl (vty T1) n →
      Pty T1 n → Pvl (vty T1) n.
  (** Beware here in Prop we use Forall, not ForallT! *)
  Variable step_vstamp : ∀ n vs s,
      nclosed vs n → nclosed_vl (vstamp vs s) n →
      Forall (flip Pvl n) vs → Pvl (vstamp vs s) n.
  Variable step_TTop : ∀ n,
      nclosed TTop n →
      Pty TTop n.
  Variable step_TBot : ∀ n,
      nclosed TBot n →
      Pty TBot n.
  Variable step_TLater : ∀ n T1,
      nclosed T1 n → nclosed (TLater T1) n →
      Pty T1 n → Pty (TLater T1) n.
  Variable step_TAll : ∀ n T1 T2,
      nclosed T1 n → nclosed T2 (S n) → nclosed (TAll T1 T2) n →
      Pty T1 n → Pty T2 (S n) → Pty (TAll T1 T2) n.
  Variable step_TTMem : ∀ n T1 T2,
      nclosed T1 n → nclosed T2 n → nclosed (TTMem T1 T2) n →
      Pty T1 n → Pty T2 n → Pty (TTMem T1 T2) n.
  Variable step_TSel : ∀ n v1,
      nclosed_vl v1 n → nclosed (TSel v1) n →
      Pvl v1 n → Pty (TSel v1) n.
  Variable step_TNat : ∀ n,
      nclosed TNat n →
      Pty TNat n.

  Fixpoint nclosed_tm_mut_ind n t: nclosed t n → Ptm t n
  with     nclosed_vl_mut_ind n v: nclosed_vl v n → Pvl v n
  with     nclosed_ty_mut_ind n T: nclosed T n → Pty T n.
  Proof.
    (* Automation risk producing circular proofs that call right away the lemma we're proving.
       Instead we want to apply one of the [case_] arguments to perform an
       inductive step, and only then call ourselves recursively. *)
    all: destruct 0; intro Hcl.
    all: let byEapply p := efeed p using (fun q => apply q) by (eauto 2; eauto 1 with fv)
    in
      match goal with
      (* Warning: add other arities as needed. *)
      | Hstep: context [?P (?c _ _ _) _] |- ?P (?c ?a1 ?a2 ?a3) _ => byEapply (Hstep n a1 a2 a3)
      | Hstep: context [?P (?c _ _) _] |- ?P (?c ?a1 ?a2) _ => byEapply (Hstep n a1 a2)
      | Hstep: context [?P (?c _) _] |- ?P (?c ?a1) _ => byEapply (Hstep n a1)
      | Hstep: context [?P (?c) _] |- ?P (?c) _ => byEapply (Hstep n)
      end.
    - induction l as [| a l]; constructor => /=; eauto 2 with fv.
  Qed.

  Lemma nclosed_syntax_mut_ind: (∀ t n, nclosed t n → Ptm t n) ∧ (∀ v n, nclosed_vl v n → Pvl v n) ∧ (∀ T n, nclosed T n → Pty T n).
  Proof.
    repeat split; intros.
    - exact: nclosed_tm_mut_ind.
    - exact: nclosed_vl_mut_ind.
    - exact: nclosed_ty_mut_ind.
  Qed.
End syntax_mut_ind_closed.
