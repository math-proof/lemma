import sympy.Basic


@[main]
private lemma main
  {a t : ℕ}
-- given
  (h₀ : a > 0)
  (h₁ : t > 1) :
-- imply
  a * t > a := by
-- proof
  nlinarith


-- created on 2026-01-13
