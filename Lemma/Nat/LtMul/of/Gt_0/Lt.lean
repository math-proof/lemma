import sympy.Basic


@[main]
private lemma main
  [Mul α] [Zero α] [Preorder α] [MulPosStrictMono α]
  {x a b : α}
-- given
  (h₀ : x > 0)
  (h₁ : a < b) :
-- imply
  a * x < b * x :=
-- proof
  mul_lt_mul_of_pos_right h₁ h₀


-- created on 2019-06-26
