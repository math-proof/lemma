import Mathlib.Data.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {a x b y : ℝ}
  -- given
  (heq : a = x)
  (hge : y ≤ b)
  -- imply
  : x + y ≤ a + b := by
  -- proof
  linarith

-- created on 2018-09-01
