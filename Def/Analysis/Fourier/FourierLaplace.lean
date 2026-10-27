import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
open MeasureTheory
open scoped FourierTransform

/-!
# Entire Fourier–Laplace transform on the real line

This module defines the complex-parameter entire extension of the real Fourier
integral in the `exp (-2π i x z)` convention and identifies its restriction to
the real axis with Mathlib's `2π`-normalised Fourier transform.

The motivating source is

* [M. Pandey and M. Radziwiłł, *L¹ means of exponential sums with multiplicative
  coefficients. I*](https://arxiv.org/abs/2307.10329) — the Fourier-transform
convention of §2 and the uses of the entire extension of a compactly supported
function in §3.

For a compactly supported integrable `f : ℝ → ℂ` the integral

```
fourierLaplace f z = ∫ x, f x * exp (-2π I x z)
```

is entire in `z : ℂ`. On the real axis it agrees with the Mathlib Fourier
integral `fourierIntegral Real.fourierChar volume f`.
-/


namespace Fourier.FourierLaplace

/-- The complex-parameter Fourier–Laplace integral
`z ↦ ∫ x, f x * exp (-2π I x z)` on `ℝ`. -/
noncomputable def fourierLaplace (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, f x * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * z)

end Fourier.FourierLaplace
