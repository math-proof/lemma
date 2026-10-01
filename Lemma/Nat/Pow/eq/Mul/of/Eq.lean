import Mathlib.Analysis.SpecialFunctions.Pow.Real
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {m n : ℕ}
  {α β M : ℝ}
-- given
  (hβ : β > 0)
  (hM : M > 0) :
-- imply
  (M / ((n : ℝ) ^ α * (m : ℝ) ^ β)) ^ (1 / β) = (M / (n : ℝ) ^ α) ^ (1 / β) / m := by
-- proof
  rw [← div_div, Real.div_rpow (div_nonneg hM.le (by positivity)) (by positivity), ← Real.rpow_mul (by positivity),
    mul_one_div_cancel hβ.ne', Real.rpow_one]


-- created on 2024-07-06
