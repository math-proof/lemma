import Lemma.Tensor.GtLength_0.of.GtLength_0
import Lemma.Tensor.LengthData.eq.Prod
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
open Tensor List


@[main]
private lemma main
-- given
  (h : s.length > 0)
  (X : Tensor α s):
-- imply
  X.data.length = s[0] * s.tail.prod := by
-- proof
  rw [LengthData.eq.Prod]
  rw [Prod.eq.Mul_ProdTail.of.GtLength_0]


@[main]
private lemma tensor
  {X : Tensor α s}
-- given
  (h : X.length > 0) :
-- imply
  have : s.length > 0 := GtLength_0.of.GtLength_0 h
  X.data.length = s[0] * s.tail.prod := by
-- proof
  intro h_length
  apply main h_length


-- created on 2025-06-29
