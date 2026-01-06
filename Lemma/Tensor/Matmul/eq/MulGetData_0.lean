import sympy.Basic
import sympy.tensor.tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α [])
  (Y : Tensor α s) :
-- imply
  X.matmul Y = X.data[0] * Y := by
-- proof
  unfold Tensor.matmul
  split_ifs
  repeat grind


-- created on 2026-01-06
