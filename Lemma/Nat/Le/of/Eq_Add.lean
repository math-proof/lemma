import sympy.sets.sets
import sympy.Basic


@[main]
private lemma bounded
  {a b d : ℝ}
-- given
  (_ha : a ≥ 0)
  (hb : b ≥ 0)
  (h : a + b = d) :
-- imply
  a ≤ d := by
-- proof
  linarith


-- created on 2023-10-03
