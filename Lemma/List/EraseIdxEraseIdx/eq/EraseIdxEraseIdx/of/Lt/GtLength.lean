import Lemma.List.EraseIdxEraseIdx.eq.EraseIdxEraseIdx.of.Le.GtLength
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h_i : i < s.length)
  (h₁ : i < j) :
-- imply
  (s.eraseIdx i).eraseIdx (j - 1) = (s.eraseIdx j).eraseIdx i := by
-- proof
  rw [EraseIdxEraseIdx.eq.EraseIdxEraseIdx.of.Le.GtLength h_i (by omega)]
  rw [EqAddSub.of.Ge (by omega)]


-- created on 2025-11-17
