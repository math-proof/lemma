import Lemma.List.ProdTake.eq.MulProdTake.of.GtLength
open List


@[main, comm]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h : i < s.length) :
-- imply
  (s.take (i + 1)).prod = s[i] * (s.take i).prod := by
-- proof
  rw [ProdTake.eq.MulProdTake.of.GtLength h]
  grind


-- created on 2025-10-27
