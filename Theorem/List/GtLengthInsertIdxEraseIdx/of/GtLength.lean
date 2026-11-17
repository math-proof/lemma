module

public import Theorem.List.LengthInsertIdxEraseIdx.eq.Length.of.GtLength

public section

open List


public theorem List.GtLengthInsertIdxEraseIdx.of.GtLength
  {d : ℕ}
  {s : List α}
-- given
  (h : s.length > d)
  (a : α) :
-- imply
  d < ((s.eraseIdx d).insertIdx d a).length := by
-- proof
  rwa [LengthInsertIdxEraseIdx.eq.Length.of.GtLength h]


-- created on 2025-10-04
