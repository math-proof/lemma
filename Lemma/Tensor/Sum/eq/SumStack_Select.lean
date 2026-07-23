import Lemma.Tensor.Sum.eq.SumStack_Select.of.GtLength
open Tensor


@[main]
private lemma main
  [AddMonoid α]
-- given
  (X : Tensor α s)
  (i : Fin s.length) :
-- imply
  X.sum i = ∑ k < s[i], X.select i k := by
-- proof
  apply Sum.eq.SumStack_Select.of.GtLength


-- created on 2026-07-22
-- updated on 2026-07-23
