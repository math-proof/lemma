import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {x a b : ℝ}
-- given
  (h₀ : x ≥ a)
  (h₁ : x ≥ b) :
-- imply
  x ≥ max a b := by
-- proof
  exact max_le h₀ h₁


-- created on 2022-01-01
