import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
-- given
  (h₀ : x < a)
  (h₁ : b < x) :
-- imply
  x ∈ Set.Ioo b a := by
-- proof
  exact ⟨h₁, h₀⟩


-- created on 2026-09-27
