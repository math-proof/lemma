import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x y : ℝ}
-- given
  (h₀ : a = b)
  (_h₁ : x > y) :
-- imply
  a * x = b * x := by
-- proof
  rw [h₀]


-- created on 2026-09-27
