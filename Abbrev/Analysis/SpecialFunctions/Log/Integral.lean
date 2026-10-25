/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Log/Integral.lean -/

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

end Real
