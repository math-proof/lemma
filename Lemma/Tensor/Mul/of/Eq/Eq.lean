import sympy.Basic
import sympy.tensor.Basic


@[main]
private lemma main
  [Mul α]
  {A B X Y : Tensor α s}
-- given
  (h₀ : A = B)
  (h₁ : X = Y) :
-- imply
  A * X = B * Y := by
-- proof
  simp_all


-- created on 2025-12-03
