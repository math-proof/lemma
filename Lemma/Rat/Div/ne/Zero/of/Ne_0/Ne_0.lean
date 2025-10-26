import sympy.Basic


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b : α}
-- given
  (h₀ : a ≠ 0)
  (h₁ : b ≠ 0) :
-- imply
  a / b ≠ 0 := by
-- proof
  simp [h₀, h₁]


-- created on 2025-03-30
