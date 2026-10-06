import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {a b c : ℝ}
  -- given
  (h : a * c = b * c)
  (hc : c ≠ 0)
  -- imply
  : a = b := by
  -- proof
  exact mul_right_cancel₀ hc h

-- created on 2019-05-22
