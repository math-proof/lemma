import Lemma.List.EraseIdxEraseIdx.of.Le.GtLength
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h_j : s.length > j)
  (h_i : i > j) :
-- imply
  (s.eraseIdx i).eraseIdx j = (s.eraseIdx j).eraseIdx (i - 1) := by
-- proof
  rw [EraseIdxEraseIdx.of.Le.GtLength h_j (by omega)]
  rw [EqAddSub.of.Ge (by omega)]


-- created on 2025-11-17
-- updated on 2025-11-24
