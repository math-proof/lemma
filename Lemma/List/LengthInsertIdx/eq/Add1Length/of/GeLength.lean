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
  (s.insertIdx i a).length = 1 + s.length := by
-- proof
  rw [LengthInsertIdx.eq.Add_Length_1.of.GeLength h]
  rw [Add.comm]


-- created on 2025-06-08
-- updated on 2026-07-12
