import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  {m n : ℕ}
  -- imply
  : x ^ m * x ^ n = x ^ (m + n) := by
  -- proof
  exact (pow_add x m n).symm

-- created on 2019-11-26
