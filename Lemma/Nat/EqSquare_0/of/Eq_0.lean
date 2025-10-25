import sympy.core.power
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x = 0) :
-- imply
  x² = 0 := by
-- proof
    -- Square both sides of the equation
  rw [h]
    -- Calculate the square of 0 and substitute back into the equation
  norm_num


-- created on 2025-04-06
