import sympy.Basic


@[main, comm 1]
private lemma main
  [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h₀ : x ≥ 0)
  (h₁ : a ≤ b) :
-- imply
  x * a ≤ x * b := by
-- proof
  exact mul_le_mul_of_nonneg_left h₁ h₀


-- created on 2024-07-01
-- updated on 2025-04-04
