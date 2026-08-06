import sympy.Basic


@[main]
private lemma main
  [MulZeroClass α] [Preorder α] [PosMulMono α]
  {a b : α}
-- given
  (h₀ : a ≥ 0)
  (h₁ : b ≥ 0) :
-- imply
  a * b ≥ 0 :=
-- proof
  mul_nonneg h₀ h₁


-- created on 2018-07-02
