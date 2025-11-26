import Lemma.List.EqTake.of.LeLength
import Lemma.List.ProdTakeDrop.eq.Get.of.GtLength
open List


@[main]
private lemma main
  [MulOneClass α]
  {s : List α}
-- given
  (h : s.length = n + 1) :
-- imply
  (s.drop n).prod = s[n] := by
-- proof
  have := ProdTakeDrop.eq.Get.of.GtLength (s := s) (i := n) (by omega)
  rw [EqTake.of.LeLength (by simp; omega)] at this
  exact this


-- created on 2025-10-28
