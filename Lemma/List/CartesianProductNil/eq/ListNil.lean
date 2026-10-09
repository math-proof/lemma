import stdlib.List
import Lemma.List.ProductNil.eq.ListNil
open List


@[path]
private lemma main :
-- imply
  [].cartesianProduct = [[]] := by
-- proof
  unfold List.cartesianProduct
  apply ProductNil.eq.ListNil


-- created on 2025-06-14
