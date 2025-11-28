import Lemma.List.ProdTakeEraseIdx.eq.MulProdTakeDrop.of.Lt.GtLength
import Lemma.List.TakeEraseIdx.eq.EraseIdxTake.of.Le
open List


@[main, comm]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h_k : s.length > k)
  (h_d : k > d) :
-- imply
  ((s.take (k + 1)).eraseIdx d).prod = ((s.eraseIdx d).take (k - 1)).prod * s[k] := by
-- proof
  rw [← TakeEraseIdx.eq.EraseIdxTake.of.Le (by omega)]
  rw [ProdTakeEraseIdx.eq.MulProdTakeDrop.of.Lt.GtLength h_k h_d]


-- created on 2025-11-28
