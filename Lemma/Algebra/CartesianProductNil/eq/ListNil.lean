import stdlib.List
import Lemma.Algebra.ProductNil.eq.ListNil
open Algebra


@[main]
private lemma main :
-- imply
  [].cartesianProduct = [[]] := by
-- proof
  unfold List.cartesianProduct
  apply ProductNil.eq.ListNil


-- created on 2025-06-14
