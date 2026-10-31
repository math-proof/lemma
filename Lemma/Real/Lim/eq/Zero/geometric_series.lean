import Mathlib.Analysis.SpecificLimits.Normed
import Def.Analysis.Real.Limits.Basic
import Initialize.Tactic.Attr.Basic


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
-- updated on 2026-10-26
