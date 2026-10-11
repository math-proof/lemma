import Mathlib
import sympy.Basic
import sympy.integrals.transforms.Scaling

/--
[Scaling](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/Scaling.lean)
-/
@[path]
private lemma fourier_comp_mul_left_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {a : ℝ}
  (ha : a ≠ 0)
  (f : ℝ → E)
  (y : ℝ) :
-- imply
  FourierTransform.fourier (fun x => f (a * x)) y =
    (|a|⁻¹ : ℝ) • FourierTransform.fourier f (y / a) := by
-- proof
  apply Fourier.Scaling.Real.fourier_comp_mul_left f ha y

/--
[Scaling](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/Scaling.lean)
-/
@[path]
private lemma fourier_comp_mul_left_of_pos_eq
-- given
  {a : ℝ}
  (ha : 0 < a)
  (f : ℝ → ℂ)
  (y : ℝ) :
-- imply
  FourierTransform.fourier (fun x => f (a * x)) y =
    ((a : ℂ)⁻¹) • FourierTransform.fourier f (y / a) := by
-- proof
  apply Fourier.Scaling.Real.fourier_comp_mul_left_of_pos f ha y

/--
[Scaling](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/Scaling.lean)
-/
@[path]
private lemma fourier_coe_comp_mul_left_of_pos_eq
-- given
  {a : ℝ}
  (ha : 0 < a)
  (f : SchwartzMap ℝ ℂ)
  (y : ℝ) :
-- imply
  FourierTransform.fourier (fun x => (f : ℝ → ℂ) (a * x)) y =
    ((a : ℂ)⁻¹) • FourierTransform.fourier (f : ℝ → ℂ) (y / a) := by
-- proof
  apply Fourier.Scaling.SchwartzMap.fourier_coe_comp_mul_left_of_pos f ha y

-- created on 2026-10-10
