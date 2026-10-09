import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a : ℝ} :
-- imply
  |x| < a ↔ x < a ∧ x > -a := by
-- proof
  rw [abs_lt]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩


-- created on 2022-01-07
