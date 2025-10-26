import sympy.core.numbers
import Mathlib.Analysis.Real.Pi.Bounds
import sympy.Basic


/--
This lemma establishes that the value of π divided by 9 is less than one-half.
The proof utilizes the known upper bound of π being less than 4 to simplify the inequality, demonstrating that π/9 < 1/2 holds true.
-/
@[main]
private lemma main:
-- imply
  π / 9 < 1 / 2 := by
-- proof
  suffices π < 9 / 2 by
    linarith
  linarith [Real.pi_lt_four]


-- created on 2025-03-24
-- updated on 2025-04-04
