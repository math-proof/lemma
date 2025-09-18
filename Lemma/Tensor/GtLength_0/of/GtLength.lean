import sympy.tensor.Basic
import Lemma.Tensor.GtLength_0.of.GtLength_0
import Lemma.Algebra.Gt_0.of.Gt
open Tensor Algebra


@[main]
private lemma main
  {t : Tensor α s}
-- given
  (h : t.length > i) :
-- imply
  s.length > 0 := by
-- proof
  have h := Gt_0.of.Gt h
  apply GtLength_0.of.GtLength_0 h


-- created on 2025-06-29
