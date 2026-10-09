import Mathlib.Analysis.SpecialFunctions.Pow.Real
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma exponent
  {x t z : ℝ}
-- given
  (ht : t ≠ 0) :
-- imply
  t ^ x * t * z = t ^ (x + 1) * z := by
-- proof
  rw [Real.rpow_add_one ht]


-- created on 2022-07-07
