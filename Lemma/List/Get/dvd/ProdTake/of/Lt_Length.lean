import Lemma.List.ProdTake.eq.MulProdTake.of.Lt_Length
open List


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h : i < s.length) :
-- imply
  s[i] ∣ (s.take (i + 1)).prod := by
-- proof
  simp [ProdTake.eq.MulProdTake.of.Lt_Length h]


-- created on 2025-11-15
