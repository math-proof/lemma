module

public import Mathlib
public import Theorem.Analysis.Fourier.Scaling.Part2
public import Theorem.Real.Fourier_UFnMul.eq.SMulFourier.of.Ne_0

public section

open scoped FourierTransform
open MeasureTheory


namespace Real

/--
[Scaling](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/Scaling.lean)
-/
public theorem fourier_comp_mul_left_of_pos
-- given
  {a : ℝ}
  (ha : 0 < a)
  (f : ℝ → ℂ)
  (y : ℝ) :
-- imply
  FourierTransform.fourier (fun x => f (a * x)) y =
    ((a : ℂ)⁻¹) • FourierTransform.fourier f (y / a) := by
-- proof
  rw [fourier_comp_mul_left (ne_of_gt ha) f y, abs_of_pos ha]
  simp [Complex.real_smul, Complex.ofReal_inv, smul_eq_mul]

end Real


-- created on 2026-10-10
-- updated on 2026-10-26
