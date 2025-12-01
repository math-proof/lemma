import sympy.Basic
import sympy.tensor.tensor


@[main]
private lemma main
  [Mul α]
-- given
  (h : s = s')
  (A B : Tensor α s) :
-- imply
  have h := congrArg (Tensor α) h
  cast h (A * B) = cast h A * cast h B := by
-- proof
  sorry


-- created on 2025-12-01
