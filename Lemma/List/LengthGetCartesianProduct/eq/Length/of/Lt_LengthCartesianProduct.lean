import Lemma.List.LengthGetProduct.eq.Length.of.Lt_LengthProduct
import Lemma.List.LengthMap.eq.Length
open List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h₀ : i < s.cartesianProduct.length) :
-- imply
  s.cartesianProduct[i].length = s.length := by
-- proof
  unfold List.cartesianProduct
  rw [LengthGetProduct.eq.Length.of.Lt_LengthProduct]
  rw [LengthMap.eq.Length]


-- created on 2025-06-29
