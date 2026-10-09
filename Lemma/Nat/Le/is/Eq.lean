import sympy.sets.sets
import sympy.Basic


@[path]
private lemma squeeze
  {x a : ℝ}
-- given
  (h₀ : x ≥ a) :
-- imply
  x ≤ a ↔ x = a := by
-- proof
  exact ⟨fun h => le_antisymm h h₀, fun h => h.le⟩


-- created on 2019-11-26
