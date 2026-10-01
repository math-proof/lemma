import sympy.sets.sets
import sympy.Basic


@[main]
private lemma squeeze
  {x a : ℤ}
-- given
  (h₀ : x ≥ a - 1) :
-- imply
  x < a ↔ x = a - 1 := by
-- proof
  exact ⟨fun h => by omega, fun h => by omega⟩


-- created on 2020-01-10
