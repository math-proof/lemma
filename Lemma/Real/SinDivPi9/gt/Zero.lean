import sympy.functions.elementary.trigonometric
import sympy.Basic


@[main]
private lemma main:
-- imply
  sin (Real.pi / 9) > 0 := by
-- proof
  have h : 0 < Real.pi / 9 := by linarith [Real.pi_pos]
  have h' : Real.pi / 9 < Real.pi := by linarith [Real.pi_pos]
  exact Real.sin_pos_of_pos_of_lt_pi h h'


-- created on 2025-03-24
-- updated on 2025-04-04
