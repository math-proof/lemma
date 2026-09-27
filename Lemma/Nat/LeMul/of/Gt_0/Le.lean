import sympy.Basic


@[main]
private lemma main
  [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
-- given
  (h₀ : x > 0)
  (h₁ : a ≤ b) :
-- imply
  a * x ≤ b * x :=
-- proof
  mul_le_mul_of_nonneg_right h₁ h₀.le


-- created on 2026-09-26
