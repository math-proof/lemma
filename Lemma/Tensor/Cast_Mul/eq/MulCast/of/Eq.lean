import sympy.Basic
import sympy.tensor.tensor


@[main]
private lemma main
  [Mul α]
-- given
  (h : s = s')
  (X : Tensor α s)
  (a : α) :
-- imply
  have h := congrArg (Tensor α) h
  cast h (X * a) = cast h A * a := by
-- proof
  sorry


-- created on 2025-12-01
