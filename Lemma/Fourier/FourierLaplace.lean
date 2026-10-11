import Mathlib
import sympy.Basic
import sympy.integrals.transforms.FourierLaplace

open Fourier.FourierLaplace
open MeasureTheory

/--
[FourierLaplace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/FourierLaplace.lean)
-/
@[path]
private lemma fourierLaplace_ofReal_eq
-- given
  (f : ℝ → ℂ)
  (r : ℝ) :
-- imply
  fourierLaplace f (r : ℂ) = Fourier.fourierIntegral Real.fourierChar volume f r := by
-- proof
  apply fourierLaplace_ofReal

/--
[FourierLaplace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/FourierLaplace.lean)
-/
@[path]
private lemma hasDerivAt_fourierLaplace_is
-- given
  {f : ℝ → ℂ}
  (hf : Integrable f)
  (hfc : HasCompactSupport f)
  (z : ℂ) :
-- imply
  HasDerivAt (fourierLaplace f)
    (∫ x : ℝ, f x * ((-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * z))) z := by
-- proof
  apply hasDerivAt_fourierLaplace hf hfc

/--
[FourierLaplace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/FourierLaplace.lean)
-/
@[path]
private lemma differentiable_fourierLaplace_is
-- given
  {f : ℝ → ℂ}
  (hf : Integrable f)
  (hfc : HasCompactSupport f) :
-- imply
  Differentiable ℂ (fourierLaplace f) := by
-- proof
  apply differentiable_fourierLaplace hf hfc

/--
[FourierLaplace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/FourierLaplace.lean)
-/
@[path]
private lemma fourierLaplace_zero_eq
-- given
  (f : ℝ → ℂ) :
-- imply
  fourierLaplace f 0 = ∫ x, f x := by
-- proof
  apply fourierLaplace_zero

/--
[FourierLaplace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/FourierLaplace.lean)
-/
@[path]
private lemma fourierLaplace_zero_function_eq
-- given
  (z : ℂ) :
-- imply
  fourierLaplace (0 : ℝ → ℂ) z = 0 := by
-- proof
  apply fourierLaplace_zero_function

-- created on 2026-10-10
