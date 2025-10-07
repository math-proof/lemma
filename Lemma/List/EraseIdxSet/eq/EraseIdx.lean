import Lemma.List.EraseIdxSet.eq.Ite_SetEraseIdx
open List


@[main]
private lemma main
-- given
  (s : List α)
  (i : ℕ)
  (x : α) :
-- imply
  (s.set i x).eraseIdx i = s.eraseIdx i := by
-- proof
  simp [EraseIdxSet.eq.Ite_SetEraseIdx]


-- created on 2025-10-07
