import Lemma.Algebra.LengthProduct.eq.ProdMap
import Lemma.Algebra.EqMapMap
open Algebra


@[main]
private lemma main
-- given
  (s : List ℕ) :
-- imply
  s.cartesianProduct.length = s.prod := by
-- proof
  unfold List.cartesianProduct
  rw [LengthProduct.eq.ProdMap]
  congr
  rw [EqMapMap]


-- created on 2025-06-11
