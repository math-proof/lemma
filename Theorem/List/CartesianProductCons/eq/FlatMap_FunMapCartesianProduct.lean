module

public import Theorem.List.ProductCons.eq.FlatMap_FunMapProduct

public section

open List


public theorem List.CartesianProductCons.eq.FlatMap_FunMapCartesianProduct
-- given
  (head : ℕ)
  (tail : List ℕ) :
-- imply
  (head :: tail).cartesianProduct = (List.range head).flatMap (fun h => tail.cartesianProduct.map (fun t => h :: t)) := by
-- proof
  unfold List.cartesianProduct
  apply ProductCons.eq.FlatMap_FunMapProduct


-- created on 2025-06-14
