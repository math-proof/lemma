import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
-- given
  (h₀ : x ≤ b)
  (h₁ : a < x) :
-- imply
  x ∈ Set.Ioc a b := by
-- proof
  exact ⟨h₁, h₀⟩


-- created on 2021-05-24
