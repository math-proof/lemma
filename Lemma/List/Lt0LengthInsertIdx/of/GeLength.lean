import Lemma.List.LengthInsertIdx.eq.Add_Length_1.of.GeLength
import Lemma.Nat.Add
import stdlib.List
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length ≥ i)
  (a : α) :
-- imply
  (s.insertIdx i a).length > 0 := by
-- proof
  rw [LengthInsertIdx.eq.Add_Length_1.of.GeLength h]
  grind


-- created on 2026-07-13
