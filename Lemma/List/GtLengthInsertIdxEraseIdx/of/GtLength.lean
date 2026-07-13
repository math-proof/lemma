import Lemma.List.LengthInsertIdxEraseIdx.eq.Length.of.GtLength
open List


@[main]
private lemma main
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
