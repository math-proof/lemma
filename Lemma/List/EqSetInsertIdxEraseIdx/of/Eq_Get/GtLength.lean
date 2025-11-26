import Lemma.List.EqSetInsertIdxEraseIdx.of.GtLength
open List


@[main]
private lemma main
  {dim : ℕ}
  {s : List α}
-- given
  (h : s.length > dim)
  (h_x : x = s[dim])
  (a : α) :
-- imply
  ((s.eraseIdx dim).insertIdx dim a).set dim x = s := by
-- proof
  subst h_x
  apply EqSetInsertIdxEraseIdx.of.GtLength h


-- created on 2025-10-10
