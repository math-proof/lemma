import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {a : ℝ}
  -- given
  (h : 0 < a)
  -- imply
  : 0 < 1 / a := by
  -- proof
  exact one_div_pos.mpr h

-- created on 2023-03-26
