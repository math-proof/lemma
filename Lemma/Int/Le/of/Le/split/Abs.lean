import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a M : ℝ}
-- given
  (h : |a| ≤ M) :
-- imply
  a ≤ M := by
-- proof
  exact (abs_le.mp h).2


@[path]
private lemma negate
  {a M : ℝ}
-- given
  (h : |a| ≤ M) :
-- imply
  -a ≤ M := by
-- proof
  linarith [(abs_le.mp h).1]


-- created on 2023-04-15
