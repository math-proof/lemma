import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


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

/-- Domain of the normalized logarithmic integral: `0 ≤ x` and `x ≠ 1`.

`1` is excluded because `1 / log t` is singular at `t = 1`; the classical
integral `∫₀ˣ dt / log t` has no finite real value at `x = 1` and is
understood as a Cauchy principal value for `x ≠ 1`.

Source: arXiv:2306.14073v1 and arXiv:2309.16007v1, classical `li(x) := PV ∫₀ˣ dt/log t`
with lower limit `0` and principal value at `t = 1`. -/
abbrev LogarithmicIntegralDomain : Type :=
  { x : ℝ // 0 ≤ x ∧ x ≠ 1 }

/-- Normalized Cauchy-principal-value logarithmic integral `li`.

For `0 ≤ x < 1`, `li x = ∫ t in 0..x, (log t)⁻¹`. For `x > 1`,
`li x = (∫ u in 0..1, ((log (1 - u))⁻¹ + (log (1 + u))⁻¹)) +
        ∫ t in 2..x, (log t)⁻¹`,
where the first integral is the paired symmetric principal value
`PV ∫₀² dt / log t = ∫₀¹ ((log (1-u))⁻¹ + (log (1+u))⁻¹) du` obtained
by `t = 1 ∓ u`. The value at `0` is `0`. The function is not defined at
`1` because the integrand is singular there. Single-point totalizations
`(log 1)⁻¹ = 0` and `(log 0)⁻¹ = 0` do not affect Lebesgue interval
integrals.

Source: arXiv:2306.14073v1 and arXiv:2309.16007v1, normalized lower limit `0`
and Cauchy principal value at `t = 1` via symmetric pairing. -/
noncomputable def logarithmicIntegral (x : LogarithmicIntegralDomain) : ℝ :=
  if x.val < 1 then
    ∫ t in (0 : ℝ)..x.val, (Real.log t)⁻¹
  else
    (∫ u in (0 : ℝ)..(1 : ℝ), ((Real.log (1 - u))⁻¹ + (Real.log (1 + u))⁻¹)) +
      ∫ t in (2 : ℝ)..x.val, (Real.log t)⁻¹

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
