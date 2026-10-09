import Mathlib.Data.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {a : ℝ}
  -- imply
  : a * a = a ^ 2 := by
  -- proof
  exact (pow_two a).symm

-- created on 2019-11-26
