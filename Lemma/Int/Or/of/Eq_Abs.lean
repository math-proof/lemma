import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : |x| = y) :
-- imply
  x = y ∨ x = -y := by
-- proof
  have hy : 0 ≤ y := h ▸ abs_nonneg x
  exact (abs_eq hy).mp h


-- created on 2026-09-27
