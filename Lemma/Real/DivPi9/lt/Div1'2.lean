import sympy.core.numbers
import Mathlib.Analysis.Real.Pi.Bounds
import sympy.Basic


@[main]
private lemma main:
-- imply
  π / 9 < 1 / 2 := by
-- proof
  linarith [Real.pi_lt_four]


-- created on 2025-03-24
-- updated on 2025-04-04
