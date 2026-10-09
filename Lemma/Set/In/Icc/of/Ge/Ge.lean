import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a b : ℝ}
-- given
  (h₀ : b ≥ x)
  (h₁ : x ≥ a) :
-- imply
  x ∈ Set.Icc a b := by
-- proof
  exact ⟨h₁, h₀⟩


-- created on 2021-04-06
