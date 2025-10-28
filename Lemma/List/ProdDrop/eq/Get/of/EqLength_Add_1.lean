import Lemma.List.EqTake.of.Ge_Length
import Lemma.List.ProdTakeDrop.eq.Get.of.Lt_Length
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
  have := ProdTakeDrop.eq.Get.of.Lt_Length (s := s) (i := n) (by omega)
  rw [EqTake.of.Ge_Length (by simp; omega)] at this
  exact this


-- created on 2025-10-28
