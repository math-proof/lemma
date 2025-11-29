import Lemma.List.ProdDrop.eq.MulProdSDrop.of.Le
import Lemma.List.ProdDropTake.eq.Get.of.GtLength
import Lemma.List.TakeTake.eq.Take.of.Gt
open List


@[main, comm]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h_i : s.length > i)
  (h : i > j) :
-- imply
  ((s.take (i + 1)).drop (j + 1)).prod = ((s.take i).drop (j + 1)).prod * s[i] := by
-- proof
  rw [ProdDrop.eq.MulProdSDrop.of.Le (show j + 1 ≤ i by omega)]
  rw [ProdDropTake.eq.Get.of.GtLength (by omega)]
  rw [TakeTake.eq.Take.of.Gt (by omega)]


-- created on 2025-11-28
