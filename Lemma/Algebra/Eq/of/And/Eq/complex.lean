import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {x y a b : ℝ}
-- given
  (h : x + I * y = a + I * b) :
-- imply
  x = a ∧ y = b := by
-- proof
  constructor
  ·
    simpa using congrArg re h
  ·
    simpa using congrArg im h


-- created on 2018-06-03
-- updated on 2026-08-20
