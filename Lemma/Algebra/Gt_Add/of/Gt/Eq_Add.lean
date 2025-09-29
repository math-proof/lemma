import sympy.Basic


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {a a' b c : α}
-- given
  (h₀ : a > a')
  (h₁ : c = a + b) :
-- imply
  c > a' + b := by
-- proof
  linarith [h₀, h₁]


-- created on 2025-03-20
