import sympy.Basic


@[main]
private lemma main
  [MulZeroClass α]
  [Preorder α]
  [PosMulStrictMono α]
  {x y : α}
-- given
  (h₀ : x > 0)
  (h₁ : y < 0) :
-- imply
  x * y < 0 :=
-- proof
  mul_neg_of_pos_of_neg h₀ h₁


-- created on 2025-03-23
