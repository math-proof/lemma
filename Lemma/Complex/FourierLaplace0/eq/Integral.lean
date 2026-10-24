import Mathlib
import sympy.Basic
import sympy.integrals.transforms.FourierLaplace
open Fourier.FourierLaplace
open MeasureTheory


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


-- created on 2026-10-10
-- updated on 2026-10-24
