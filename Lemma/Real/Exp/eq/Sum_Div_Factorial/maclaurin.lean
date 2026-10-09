import Mathlib
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  -- imply
  : Real.exp x = ∑' n, x ^ n / (n.factorial : ℝ) := by
  -- proof
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]


-- created on 2026-10-09
