From D Require Import prelude.
From D.Dot Require Import fundamental.
From D.Dot.examples Require positive_div from_pdot_mutual_rec_sem.

Print Assumptions type_soundness.
Print Assumptions path_normalization.
Print Assumptions positive_div.examples.miniVSafe.
Print Assumptions positive_div.examples.posModVSafe.
Print Assumptions from_pdot_mutual_rec_sem.pcoreSafe.

From D.Dot.examples Require list.

Print Assumptions list.clListTypNat3.
