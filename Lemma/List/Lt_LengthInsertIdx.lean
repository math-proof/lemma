import stdlib.List
import Lemma.List.LengthInsertIdx.eq.Add1Length.of.Le_Length
import Lemma.Nat.LtVal
open List Nat


@[main]
private lemma main
  {v : List α}
-- given
  (i : Fin v.length)
  (a : α) :
-- imply
  i < (v.insertIdx i a).length := by
-- proof
  have h_i := LtVal i
  rw [LengthInsertIdx.eq.Add1Length.of.Le_Length]
  repeat linarith


-- created on 2025-10-05
