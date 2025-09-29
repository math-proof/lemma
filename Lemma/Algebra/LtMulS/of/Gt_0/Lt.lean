import sympy.Basic


/--
Given `x > 0` and `a < b`, this lemma proves that `x * a < x * b` by leveraging the strict monotonicity of multiplication by positive elements, as defined by the `PosMulStrictMono` typeclass.
It ensures that multiplying both sides of a strict inequality by a positive element preserves the inequality direction.
-/
@[main]
private lemma main
  [Mul α] [Zero α] [Preorder α] [PosMulStrictMono α]
  {x a b : α}
-- given
  (h₀ : x > 0)
  (h₁ : a < b) :
-- imply
  x * a < x * b := by
-- proof
  exact mul_lt_mul_of_pos_left h₁ h₀


-- created on 2024-07-01
-- updated on 2025-04-04
