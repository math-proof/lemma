import sympy.functions.elementary.trigonometric
import Lemma.Algebra.DivPi9.lt.Div1'2
import Lemma.Algebra.Lt.of.Lt.Lt
open Algebra


/--
This lemma establishes that the sine of π divided by 9 is less than 1/2.
The proof leverages the inequality sin(x) < x for all positive x less than π/2, applying it to x = π/9.
By combining this with the previously established fact that π/9 < 1/2, the transitivity of inequalities yields the desired result.
-/
@[main]
private lemma main:
-- imply
  sin (π / 9) < 1 / 2 := by
-- proof
  -- Use the inequality sin(x) < x for 0 < x < π/2
  have h_Gt : π / 9 > 0 := by linarith [Real.pi_pos]
  have h_Lt : sin (π / 9) < π / 9 := Real.sin_lt h_Gt
  -- Combine the inequalities to show sin(π/9) < π/9 < 1/2
  -- linarith [Real.pi_pos]
  have := Lt.of.Lt.Lt h_Lt DivPi9.lt.Div1'2
  assumption


-- created on 2025-03-24
-- updated on 2025-04-04
