import Lemma.List.EqSetInsertIdxEraseIdx.of.GtLength
open List


@[main]
private lemma main
  {d : ℕ}
  {s : List α}
-- given
  (h : s.length > d)
  (h_x : x = s[d])
  (a : α) :
-- imply
  ((s.eraseIdx d).insertIdx d a).set d x = s := by
-- proof
  subst h_x
  apply EqSetInsertIdxEraseIdx.of.GtLength h


-- created on 2025-10-10
