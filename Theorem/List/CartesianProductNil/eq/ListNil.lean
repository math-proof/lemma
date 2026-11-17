module

public import Def.Data.List.List.Basic
public import Theorem.List.ProductNil.eq.ListNil

public section

open List


public theorem List.CartesianProductNil.eq.ListNil :
-- imply
  [].cartesianProduct = [[]] := by
-- proof
  unfold List.cartesianProduct
  apply ProductNil.eq.ListNil


-- created on 2025-06-14
