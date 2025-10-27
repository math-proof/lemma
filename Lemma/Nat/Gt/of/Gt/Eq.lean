import sympy.Basic


@[main]
private lemma main
  [LT α]
  { x a b : α}
-- given
  (h₀ : b > x)
  (h₁ : a = x) :
-- imply
  b > a := by
-- proof
  aesop


-- created on 2025-10-01
