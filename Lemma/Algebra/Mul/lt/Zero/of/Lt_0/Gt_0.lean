import sympy.Basic


@[main]
private lemma int
  {x y : ℤ}
-- given
  (h₀ : x < 0)
  (h₁ : y > 0) :
-- imply
  x * y < 0 :=
-- proof
  Int.mul_neg_of_neg_of_pos h₀ h₁


@[main]
private lemma main
  [MulZeroClass α]
  [Preorder α]
  [MulPosStrictMono α]
  {x y : α}
-- given
  (h₀ : x < 0)
  (h₁ : y > 0) :
-- imply
  x * y < 0 :=
-- proof
  mul_neg_of_neg_of_pos h₀ h₁


-- created on 2025-03-23
