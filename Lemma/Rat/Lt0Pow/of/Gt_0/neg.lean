import Mathlib.Data.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  {n : ℤ}
  -- given
  (_hn : n < 0)
  (hx : 0 < x)
  -- imply
  : 0 < x ^ n := by
  -- proof
  positivity

-- created on 2023-04-15
