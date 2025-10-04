import Lemma.List.LengthInsertIdxEraseIdx.eq.Length.of.Lt_Length
open List


@[main]
private lemma main
  {dim : ℕ}
  {s : List α}
-- given
  (h : dim < s.length)
  (a : α) :
-- imply
  dim < ((s.eraseIdx dim).insertIdx dim a).length := by
-- proof
  rwa [LengthInsertIdxEraseIdx.eq.Length.of.Lt_Length h]


-- created on 2025-10-04
