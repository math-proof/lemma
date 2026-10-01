import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x a b : ℝ}
-- given
  (h₀ : a ≤ x)
  (h₁ : b ≤ x) :
-- imply
  max a b ≤ x := by
-- proof
  exact max_le h₀ h₁


-- created on 2023-03-26
