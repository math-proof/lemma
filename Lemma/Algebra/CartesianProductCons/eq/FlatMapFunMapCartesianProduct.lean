import Lemma.Algebra.ProductCons.eq.FlatMapFunMapProduct
open Algebra


@[main]
private lemma main
-- given
  (head : ℕ)
  (tail : List ℕ) :
-- imply
  (head :: tail).cartesianProduct = (List.range head).flatMap (fun h => tail.cartesianProduct.map (fun t => h :: t)) := by
-- proof
  unfold List.cartesianProduct
  apply ProductCons.eq.FlatMapFunMapProduct


-- created on 2025-06-14
