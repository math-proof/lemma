import Lemma.List.ProdTake.eq.Mul_ProdDropTake.of.Ge
import Lemma.List.Slice.eq.DropTake
open List


@[main]
private lemma main
  [Monoid α]
-- given
  (h : i ≥ j)
  (s : List α) :
-- imply
  (s.take i).prod = (s.take j).prod * (s.slice j i).prod := by
-- proof
  rw [ProdTake.eq.Mul_ProdDropTake.of.Ge h]
  rw [Slice.eq.DropTake]


-- created on 2025-06-14
-- updated on 2025-11-28
