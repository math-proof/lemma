import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
-- given
  (h₀ : x < b)
  (h₁ : x ≥ a) :
-- imply
  x ∈ Set.Ico a b := by
-- proof
  exact ⟨h₁, h₀⟩


-- created on 2026-09-27
