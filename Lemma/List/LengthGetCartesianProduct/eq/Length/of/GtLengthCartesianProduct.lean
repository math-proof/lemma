import Lemma.List.LengthGetProduct.eq.Length.of.GtLengthProduct
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
  unfold List.cartesianProduct at *
  rw [LengthGetProduct.eq.Length.of.GtLengthProduct h₀]
  rw [LengthMap.eq.Length]


-- created on 2025-06-29
-- updated on 2026-08-24
