import sympy.Basic


@[main]
private lemma main
  [MulZeroClass α] [Preorder α] [PosMulStrictMono α]
  {a b : α}
-- given
  (h₀ : a > 0)
  (h₁ : b > 0) :
-- imply
  a * b > 0 :=
-- proof
  mul_pos h₀ h₁


-- created on 2024-11-25
-- updated on 2026-08-07
