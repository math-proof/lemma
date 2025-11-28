import sympy.tensor.Basic
import sympy.tensor.functions
import Lemma.List.EqEraseIdx.of.LeLength
open List


@[main, comm]
private lemma main
  {d : ℕ}
-- given
  (h : s.length ≤ d)
  (X : Tensor α s) :
-- imply
  (cast (congrArg (Tensor α) (Eq_EraseIdx.of.LeLength h)) X).keepdim = X := by
-- proof
  sorry


-- created on 2025-11-28
