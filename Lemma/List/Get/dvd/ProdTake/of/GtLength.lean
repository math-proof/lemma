import Lemma.List.ProdTake.eq.MulProdTake.of.GtLength
open List


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  s[i] ∣ (s.take (i + 1)).prod := by
-- proof
  simp [ProdTake.eq.MulProdTake.of.GtLength h]


-- created on 2025-11-15
