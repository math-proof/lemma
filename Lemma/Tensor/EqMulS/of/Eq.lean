import sympy.tensor.Basic
import sympy.Basic


@[main]
private lemma main
  [Mul α]
  {A B : Tensor α n}
-- given
  (h : A = B)
  (x : α) :
-- imply
  A * x = B * x := by
-- proof
  rw [h]


-- created on 2025-12-01
