import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a b : ℝ}
-- given
  (h₀ : x > b)
  (h₁ : a ≥ x) :
-- imply
  x ∈ Set.Ioc b a := by
-- proof
  exact ⟨h₀, h₁⟩


-- created on 2021-04-13
