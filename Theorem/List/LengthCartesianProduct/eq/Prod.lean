module

public import Theorem.List.LengthProduct.eq.ProdMap
public import Theorem.List.EqMapMap

public section

open List


public theorem List.LengthCartesianProduct.eq.Prod
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
