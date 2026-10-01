import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b M : ℝ}
-- given
  (h : min a b = M) :
-- imply
  a ≥ M := by
-- proof
  exact h ▸ min_le_left a b


-- created on 2026-09-27
