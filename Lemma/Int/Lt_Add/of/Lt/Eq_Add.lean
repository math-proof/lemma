import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {a a' b c : α}
-- given
  (h₀ : a < a')
  (h₁ : c = a + b) :
-- imply
  c < a' + b := by
-- proof
  grind


-- created on 2025-03-20
-- updated on 2025-10-25
