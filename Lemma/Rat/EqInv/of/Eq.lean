import Mathlib.Data.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
  -- given
  (h : a = b)
  -- imply
  : a⁻¹ = b⁻¹ := by
  -- proof
  exact congr_arg Inv.inv h

-- created on 2019-05-22
