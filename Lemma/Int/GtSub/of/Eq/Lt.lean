import sympy.Basic


@[main]
private lemma main
  {x y a b : ℝ}
-- given
  (h₀ : y = x)
  (h₁ : a < b) :
-- imply
  x - a > y - b := by
-- proof
  rw [h₀]
  linarith


-- created on 2026-09-27
