import sympy.Basic


@[main, comm 2]
private lemma main
  [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : x ≥ 0) :
-- imply
  a * x ≤ b * x :=
-- proof
  mul_le_mul_of_nonneg_right h₀ h₁


-- created on 2024-07-01
