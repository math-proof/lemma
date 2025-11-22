import Lemma.List.EraseIdxSet.eq.Ite_SetEraseIdx
open List


@[main]
private lemma main
-- given
  (h : i > j)
  (s : List α)
  (a : α) :
-- imply
  (s.set i a).eraseIdx j = (s.eraseIdx j).set (i - 1) a := by
-- proof
  rw [EraseIdxSet.eq.Ite_SetEraseIdx]
  grind


-- created on 2025-11-22
