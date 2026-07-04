import Lemma.Tensor.LengthTranspose.eq.Length.of.Gt_0.Gt_0
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
-- given
  (h : s.length > 2)
  (X : Tensor α s) :
-- imply
  Xᵀ.length = X.length := by
-- proof
  unfold Tensor.T
  rw [LengthTranspose.eq.Length.of.Gt_0.Gt_0]
  repeat grind


-- created on 2026-07-04
