import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (ha : a > 0) :
-- imply
  x * a > 0 ↔ x > 0 := by
-- proof
  exact ⟨fun h => by nlinarith, fun h => mul_pos h ha⟩


-- created on 2026-09-27
