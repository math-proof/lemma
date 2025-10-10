import Lemma.List.EqSetInsertIdxEraseIdx.of.Lt_Length
open List


@[main]
private lemma main
  {dim : ℕ}
  {s : List α}
-- given
  (h : dim < s.length)
  (h_x : x = s[dim])
  (a : α) :
-- imply
  ((s.eraseIdx dim).insertIdx dim a).set dim x = s := by
-- proof
  subst h_x
  apply EqSetInsertIdxEraseIdx.of.Lt_Length h


-- created on 2025-10-10
