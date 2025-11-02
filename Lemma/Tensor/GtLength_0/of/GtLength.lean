import sympy.tensor.Basic
import Lemma.Tensor.GtLength_0.of.GtLength_0
import Lemma.Nat.Gt_0.of.Gt
open Tensor Nat


@[main]
private lemma main
  {X : Tensor α s}
-- given
  (h : X.length > i) :
-- imply
  s.length > 0 := by
-- proof
  have h := Gt_0.of.Gt h
  apply GtLength_0.of.GtLength_0 h


-- created on 2025-06-29
