import sympy.tensor.Basic
import Lemma.List.EqEraseIdx.of.LeLength
import sympy.tensor.functions
open List


@[main]
private lemma main
  [NeZero s.prod]
  [LT α] [DecidableLT α]
-- given
  (h : s.length ≤ d)
  (X : Tensor α s) :
-- imply
  X.max d = cast (congrArg (Tensor α) (EqEraseIdx.of.LeLength h).symm) X := by
-- proof
  unfold Tensor.max Tensor.aminmax
  split_ifs with h_0
  ·
    omega
  ·
    rfl


-- created on 2025-12-04
