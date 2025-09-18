import Lemma.Basic


/--
Given elements `a`, `b`, and `x` in a preordered algebraic structure with strictly monotonic multiplication by positive elements, if `a` is less than `b` and `x` is positive, then multiplying both sides of the inequality by `x` preserves the strict inequality.
This lemma is a direct application of the `mul_lt_mul_of_pos_right` property, leveraging the `MulPosStrictMono` class to ensure the multiplication respects the order.
-/
@[main]
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
