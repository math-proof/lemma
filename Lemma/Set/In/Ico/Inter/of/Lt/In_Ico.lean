import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b c x : ℤ}
-- given
  (h₀ : x < c)
  (h₁ : x ∈ Set.Ico a b) :
-- imply
  x ∈ Set.Ico a (min b c) := by
-- proof
  exact ⟨h₁.1, lt_min h₁.2 h₀⟩


-- created on 2026-09-27
