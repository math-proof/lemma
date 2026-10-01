import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x y z : ℝ}
-- given
  (h₀ : y ≥ x)
  (h₁ : z ≥ x) :
-- imply
  min y z ≥ x := by
-- proof
  exact le_min h₀ h₁


-- created on 2023-03-26
