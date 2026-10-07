import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : a < b) :
-- imply
  (a + b) / 2 ∈ Ioo a b := by
-- proof
  constructor <;> linarith


-- created on 2026-10-03
