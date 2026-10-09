import Mathlib.Data.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {a b d : ℝ}
  -- given
  (_ha : 0 ≤ a)
  (hb : 0 ≤ b)
  (h : a + b = d)
  -- imply
  : a ≤ d := by
  -- proof
  linarith

-- created on 2023-10-03
