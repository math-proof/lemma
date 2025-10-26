import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b c : α}
-- given
  (h₀ : a ≥ 0)
  (h₁ : c = a + b) :
-- imply
  c ≥ b := by
-- proof
  grind


-- created on 2025-03-20
-- updated on 2025-10-26
