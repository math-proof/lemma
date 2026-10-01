import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : a ≥ b)
  (h₁ : x ∈ Set.Icc a b) :
-- imply
  x = a := by
-- proof
  exact le_antisymm (le_trans h₁.2 h₀) h₁.1


-- created on 2023-10-03
