import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.Wiman.CorrectedEstimateAbsorption

open Complex.Wiman.CorrectedEstimateAbsorption

/--
[eventually_absorb_corrected_wiman_exponent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CorrectedEstimateAbsorption.lean)
-/
@[path]
private lemma eventually_absorb_corrected_wiman_exponent_eq
-- given
  (C : ℝ)
  (hC : 0 < C) :
-- imply
  ∃ U : ℝ, 1 < U ∧ ∀ μ A : ℝ,
    U ≤ μ → μ ≤ A →
      A ≤ C * μ * (1 + Real.log A ^ (81 / 128 : ℝ)) →
        A ≤ μ * Real.log μ ^ (2 / 3 : ℝ) := by
-- proof
  apply eventually_absorb_corrected_wiman_exponent C hC


-- created on 2026-10-10
