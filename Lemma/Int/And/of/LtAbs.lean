import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (h : |x| < a) :
-- imply
  x < a ∧ x > -a := by
-- proof
  exact ⟨(abs_lt.mp h).2, (abs_lt.mp h).1⟩


-- created on 2026-09-27
