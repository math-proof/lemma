/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/Scaling.lean -/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open scoped FourierTransform
open MeasureTheory

namespace Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Fourier transform of a dilated function: scaling `x ↦ f (a * x)` by
`a ≠ 0` scales the transform by `|a|⁻¹` and dilates frequencies by `a⁻¹`.
No integrability hypothesis is needed because Mathlib's Bochner integral is
totalized, so the identity also uses that convention for nonintegrable
functions. -/
theorem fourier_comp_mul_left (f : ℝ → E) {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    𝓕 (fun x => f (a * x)) y = (|a|⁻¹ : ℝ) • 𝓕 f (y / a) := by
  simp only [Real.fourier_real_eq]
  let g : ℝ → E := fun v => (𝐞 (-(v * (y / a)))) • f v
  have hg : ∀ v, g (a * v) = (𝐞 (-(v * y))) • f (a * v) := by
    intro v
    simp only [g]
    congr 1
    congr 1
    field_simp
  simp_rw [← hg]
  rw [Measure.integral_comp_mul_left g a, abs_inv]

/-- Dilation by a positive factor, with the real scalar `a⁻¹` written as a
complex scalar `(a : ℂ)⁻¹`. -/
theorem fourier_comp_mul_left_of_pos (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (y : ℝ) :
    𝓕 (fun x => f (a * x)) y = ((a : ℂ)⁻¹) • 𝓕 f (y / a) := by
  rw [fourier_comp_mul_left f (ne_of_gt ha) y, abs_of_pos ha]
  change (a⁻¹ : ℝ) • 𝓕 f (y / a) = ((a : ℂ)⁻¹) • 𝓕 f (y / a)
  simp only [Complex.real_smul, Complex.ofReal_inv, smul_eq_mul]

end Real

namespace SchwartzMap

/-- Dilation of a Schwartz function by a positive factor, as coerced functions. -/
theorem fourier_coe_comp_mul_left_of_pos (f : SchwartzMap ℝ ℂ) {a : ℝ} (ha : 0 < a)
    (y : ℝ) :
    𝓕 (fun x => (f : ℝ → ℂ) (a * x)) y
      = ((a : ℂ)⁻¹) • 𝓕 (f : ℝ → ℂ) (y / a) :=
  Real.fourier_comp_mul_left_of_pos (f : ℝ → ℂ) ha y

end SchwartzMap
