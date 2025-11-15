import Lemma.Tensor.Sum.eq.Sum_Select.of.GtLength
open Tensor


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (X : Tensor α s)
  (i : Fin s.length) :
-- imply
  X.sum i = ∑ k : Fin s[i], X.select i k := by
-- proof
  apply Sum.eq.Sum_Select.of.GtLength


-- created on 2025-11-06
-- updated on 2025-11-15
