import Lemma.List.EraseIdx.eq.AppendEraseIdxTake.of.Lt
import Lemma.List.ProdAppend.eq.MulProdS
open List


@[main]
private lemma main
  [Monoid α]
-- given
  (h : i < d)
  (s : List α) :
-- imply
  (s.eraseIdx i).prod = ((s.take d).eraseIdx i).prod * (s.drop d).prod := by
-- proof
  rw [EraseIdx.eq.AppendEraseIdxTake.of.Lt h]
  rw [MulProdS.eq.ProdAppend]


-- created on 2025-11-03
