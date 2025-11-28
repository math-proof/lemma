import Lemma.List.DropEraseIdx.eq.AppendDropTake.of.Ge
import Lemma.List.ProdAppend.eq.MulProdS
open List


@[main]
private lemma main
  [Monoid α]
-- given
  (h : i ≥ j)
  (s : List α) :
-- imply
  ((s.eraseIdx i).drop j).prod = ((s.take i).drop j).prod * (s.drop (i + 1)).prod := by
-- proof
  rw [DropEraseIdx.eq.AppendDropTake.of.Ge h]
  rw [ProdAppend.eq.MulProdS]


-- created on 2025-11-21
