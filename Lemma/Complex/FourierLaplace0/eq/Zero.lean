import Mathlib
import sympy.Basic
import sympy.integrals.transforms.FourierLaplace
open Fourier.FourierLaplace
open MeasureTheory


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
-- updated on 2026-10-24
