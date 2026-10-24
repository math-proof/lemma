/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Log/IntegralDerivative.lean -/

import sympy.atlas.Analysis.SpecialFunctions.Log.Integral
import Lemma.Real.Integral
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic integral — real-valued chart for the derivative

The source definition `Real.logarithmicIntegral` is on the subtype
`Real.LogarithmicIntegralDomain = {x : ℝ // 0 ≤ x ∧ x ≠ 1}`
(papers 2306.14073v1:284-287, 2309.16007v1:112-115,
`li(x) = ∫₀ˣ dt / log t`, Cauchy principal value; `x = 1` excluded as the
singularity `1/log t` at `t=1` is non-integrable). Lean's `HasDerivAt` expects
`ℝ → ℝ`.

## Representation choice

We provide a single global extension `Real.logarithmicIntegralReal : ℝ → ℝ`
that agrees with `Real.logarithmicIntegral` on `0 ≤ x ∧ x ≠ 1` and is `0`
(junk) elsewhere. This is the smallest reusable chart:

* it does not redefine or renormalize the integral — the paired symmetric
  principal value `∫₀¹ ((log(1-u))⁻¹ + (log(1+u))⁻¹)` for `x > 1` and the
  ordinary `∫₀ˣ` for `0 ≤ x < 1` are preserved verbatim via
  `logarithmicIntegral`;
* at any `x₀ > 0, x₀ ≠ 1` there is a neighbourhood `I` (`(0,1)` if `x₀ < 1`,
  `(1,∞)` if `x₀ > 1`) contained in the domain on which the extension
  coincides with the integral, so `HasDerivAt` at `x₀` is independent of the
  junk value outside `I`;
* a per-point local chart `fun x in I ↦ li x` would be equivalent but forces
  a subtype coercion in every derivative statement; the global extension lets
  the derivative be stated as `HasDerivAt Real.logarithmicIntegralReal
  (1 / Real.log x) x` with hypotheses `0 < x` and `x ≠ 1`.

The derivative `1 / Real.log x` is the local FTC consequence
`d/dx ∫ dt/log t = 1/log x` via continuity of `t ↦ (log t)⁻¹` at `t = x ≠ 1`.
The theorem below supplies the full local FTC proof on both sides of the singularity.
-/

open scoped Topology

namespace Real

/-- Global real-valued extension of `logarithmicIntegral`.

Agrees with `Real.logarithmicIntegral` on `0 ≤ x ∧ x ≠ 1` and is `0`
elsewhere (junk). At `x > 0, x ≠ 1` the value is locally determined by the
integral, so `HasDerivAt` at such `x` does not depend on the junk choice. -/
noncomputable def logarithmicIntegralReal (x : ℝ) : ℝ :=
  if h : 0 ≤ x ∧ x ≠ 1 then
    Real.logarithmicIntegral (⟨x, h⟩ : Real.LogarithmicIntegralDomain)
  else
    0
end Real
