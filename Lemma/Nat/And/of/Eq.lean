import sympy.sets.sets
import sympy.Basic


@[main]
private lemma squeeze
  {x y : ℝ}
-- given
  (h : x = y) :
-- imply
  x ≤ y ∧ x ≥ y := by
-- proof
  exact ⟨h.le, h.ge⟩


-- created on 2026-09-27
