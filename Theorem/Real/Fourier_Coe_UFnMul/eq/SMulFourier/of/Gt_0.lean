module

public import Mathlib
public import Theorem.Analysis.Fourier.Scaling.Part2
public import Theorem.Real.Fourier_UFnMul.eq.SMulFourier.of.Gt_0

public section

open scoped FourierTransform
open MeasureTheory


namespace SchwartzMap

/--
[Scaling](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/Scaling.lean)
-/
public theorem fourier_coe_comp_mul_left_of_pos
-- given
  {a : ℝ}
  (ha : 0 < a)
  (f : SchwartzMap ℝ ℂ)
  (y : ℝ) :
-- imply
  FourierTransform.fourier (fun x => (f : ℝ → ℂ) (a * x)) y =
    ((a : ℂ)⁻¹) • FourierTransform.fourier (f : ℝ → ℂ) (y / a) :=
-- proof
  Real.fourier_comp_mul_left_of_pos ha (f : ℝ → ℂ) y

end SchwartzMap


-- created on 2026-10-10
-- updated on 2026-10-26
