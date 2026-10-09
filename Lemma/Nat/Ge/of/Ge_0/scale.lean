import Mathlib.Data.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {x t : ℝ}
  -- given
  (hx : 0 ≤ x)
  (ht : 1 ≤ t)
  -- imply
  : 0 ≤ t * x := by
  -- proof
  have h1 : 0 ≤ t := by linarith
  exact mul_nonneg h1 hx

-- created on 2020-02-03
