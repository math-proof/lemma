import Lemma.List.LengthInsertIdx.eq.Add_Length_1.of.GeLength
import Def.Data.List.List.Part5
open List Nat


@[path]
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
-- updated on 2026-10-26
