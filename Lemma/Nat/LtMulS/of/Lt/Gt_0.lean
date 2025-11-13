import sympy.Basic


@[main, comm 2]
private lemma main
  [Mul α] [Zero α] [Preorder α] [MulPosStrictMono α]
  {x a b : α}
-- given
  (h₀ : a < b)
  (h₁ : x > 0) :
-- imply
  a * x < b * x :=
-- proof
  mul_lt_mul_of_pos_right h₀ h₁


-- created on 2024-07-01
-- updated on 2025-07-06
