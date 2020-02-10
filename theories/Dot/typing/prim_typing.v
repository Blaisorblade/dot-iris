From D.Dot Require Import syn.
Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

Inductive un_op_syntype : un_op → base_ty → base_ty → Set :=
| ty_unot : un_op_syntype unot tbool tbool.

Inductive bin_op_syntype : bin_op → base_ty → base_ty → base_ty → Set :=
| ty_beq_bool : bin_op_syntype beq    tbool tbool tbool
| ty_beq_nat  : bin_op_syntype beq    tnat  tnat  tbool
| ty_blt      : bin_op_syntype blt    tnat  tnat  tbool
| ty_ble      : bin_op_syntype ble    tnat  tnat  tbool
| ty_bplus    : bin_op_syntype bplus  tnat  tnat  tnat
| ty_btimes   : bin_op_syntype btimes tnat  tnat  tnat.
