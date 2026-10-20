import Mathlib.Analysis.SpecificLimits.Normed
import sympy.series.limits
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h₀ : |x| < 1) :
-- imply
  lim [(n : ℕ) → ∞] x ^ n = 0 := by
-- proof
  apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one h₀


-- created on 2023-04-15
-- updated on 2026-10-17
