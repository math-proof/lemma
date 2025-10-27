import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b c : α}
-- given
  (h₀ : c = a + b)
  (h₁ : b < 0) :
-- imply
  c < a := by
-- proof
  grind


-- created on 2025-03-20
-- updated on 2025-10-26
