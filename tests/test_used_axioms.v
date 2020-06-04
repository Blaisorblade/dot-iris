From D Require Import prelude.
From D.Dot Require Import fundamental.
From D.Dot.examples Require positive_div small_sem_ex from_pdot_mutual_rec_sem.

Print Assumptions type_soundness.
Print Assumptions path_normalization.
Print Assumptions small_sem_ex.miniVSafe.
Print Assumptions positive_div.posModVSafe.
Print Assumptions from_pdot_mutual_rec_sem.pCoreClosedClientSafe.

From D.Dot.examples Require list from_pdot_mutual_rec.

Print Assumptions list.clListTypNat3.
Print Assumptions from_pdot_mutual_rec.fromPDotPaperTyp.
