import Lemma.List.ProdDrop.eq.MulProdSDrop.of.Le
import Lemma.List.ProdDropTake.eq.Get.of.GtLength
import Lemma.List.TakeTake.eq.Take.of.Gt
open List


@[main, comm]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h_d : s.length > d)
  (h : k < d) :
-- imply
  ((s.take (d + 1)).drop (k + 1)).prod = ((s.take d).drop (k + 1)).prod * s[d] := by
-- proof
  rw [ProdDrop.eq.MulProdSDrop.of.Le (show k + 1 ≤ d by omega)]
  rw [ProdDropTake.eq.Get.of.GtLength (by omega)]
  rw [TakeTake.eq.Take.of.Gt (by omega)]


-- created on 2025-11-28
