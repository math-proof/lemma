import stdlib.List
import Lemma.List.LengthInsertIdx.eq.Add1Length.of.Le_Length
open List


@[main]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length)
  (a : α) :
-- imply
  i < (s.insertIdx i a).length := by
-- proof
  have h_i := i.isLt
  rw [LengthInsertIdx.eq.Add1Length.of.Le_Length]
  repeat linarith


-- created on 2025-10-05
