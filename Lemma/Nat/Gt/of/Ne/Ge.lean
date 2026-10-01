import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (h₀ : x ≠ a)
  (h₁ : x ≥ a) :
-- imply
  x > a := by
-- proof
  exact lt_of_le_of_ne h₁ (Ne.symm h₀)


-- created on 2023-04-13
