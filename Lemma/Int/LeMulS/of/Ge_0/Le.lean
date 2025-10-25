import sympy.Basic


/--
This lemma states that multiplying both sides of an inequality by a non-negative element preserves the inequality.
Specifically, if `x ≥ 0` and `a ≤ b`, then `x * a ≤ x * b`.
This holds in a preordered algebraic structure where multiplication by non-negative elements is monotonic.
-/
@[main]
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
