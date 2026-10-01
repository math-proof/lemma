import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a M : ℝ}
-- given
  (h : |a| ≤ M) :
-- imply
  a ≥ -M := by
-- proof
  exact (abs_le.mp h).1


@[main]
private lemma negate
  {a M : ℝ}
-- given
  (h : |a| ≤ M) :
-- imply
  -a ≥ -M := by
-- proof
  linarith [(abs_le.mp h).2]


-- created on 2026-09-27
