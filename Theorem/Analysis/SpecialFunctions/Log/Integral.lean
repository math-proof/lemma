import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Def.Analysis.SpecialFunctions.Log.Integral.Part2
/-!
# Logarithmic integral (normalized principal value)

Classical lowercase logarithmic integral `li(x) := ∫₀ˣ dt / log t` in the
normalization used by arXiv:2306.14073v1 and arXiv:2309.16007v1. The real-valued
interpretation is the Cauchy principal value at the non-integrable singularity
`t = 1`. The function is defined on `{x : ℝ // 0 ≤ x ∧ x ≠ 1}`; the point
`x = 1` is excluded because `1 / log t` has a non-integrable singularity
there. At `x = 0` the value is `0`, as the integral over a degenerate interval
vanishes. For `x > 1` the principal value is represented by the paired form
symmetric about `1`, not by the raw interval integral `∫₀ˣ`, which Mathlib
totalizes via `inv 0 = 0` and Lebesgue measure-zero modifications at isolated
points. The paired symmetric integral is Lebesgue-equivalent to
`lim_{ε → 0⁺} (∫₀^{1-ε} + ∫_{1+ε}²)`.
-/


namespace Real

/-- `li` vanishes at the canonical zero of its domain.

Source: `∫₀⁰ = 0` for Lebesgue interval integrals; holds for any domain
proof `hx` with `x = 0`. -/
@[simp]
theorem logarithmicIntegral_zero {hx : 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≠ (1 : ℝ)} :
    logarithmicIntegral ⟨(0 : ℝ), hx⟩ = 0 := by
  simp [logarithmicIntegral]

/-- Unfolding for the lower branch `x < 1`.

Source: Direct unfolding of the `x < 1` branch of the piecewise definition. -/
theorem logarithmicIntegral_of_lt_one {x : LogarithmicIntegralDomain} (hx : x.val < 1) :
    logarithmicIntegral x = ∫ t in (0 : ℝ)..x.val, (Real.log t)⁻¹ := by
  simp [logarithmicIntegral, hx]

/-- Unfolding for the upper branch `1 < x`.

The paired integral `∫₀¹ ((log (1 - u))⁻¹ + (log (1 + u))⁻¹)` is the
symmetric principal value `PV ∫₀²`.

Source: Direct unfolding of the `x > 1` branch; `¬ x < 1` from `1 < x`. -/
theorem logarithmicIntegral_of_one_lt {x : LogarithmicIntegralDomain} (hx : 1 < x.val) :
    logarithmicIntegral x =
      (∫ u in (0 : ℝ)..(1 : ℝ), ((Real.log (1 - u))⁻¹ + (Real.log (1 + u))⁻¹)) +
        ∫ t in (2 : ℝ)..x.val, (Real.log t)⁻¹ := by
  have h : ¬ x.val < 1 := not_lt.mpr hx.le
  simp [logarithmicIntegral, h]

end Real
