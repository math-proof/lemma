import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x y : ℝ}
-- given
  (h₀ : x < y)
  (h₁ : y ∈ Set.Icc a b) :
-- imply
  x < b := by
-- proof
  apply lt_of_lt_of_le h₀ h₁.2


-- created on 2020-11-25
