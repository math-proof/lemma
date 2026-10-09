import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y a b : ℝ}
-- given
  (h₀ : a = b)
  (_h₁ : x < y) :
-- imply
  a / (y - x) = b / (y - x) := by
-- proof
  rw [h₀]


-- created on 2019-04-18
