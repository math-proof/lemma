import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
  {n : ℕ}
  -- imply
  : (x * y) ^ n = x ^ n * y ^ n := by
  -- proof
  exact mul_pow x y n

-- created on 2019-11-26
