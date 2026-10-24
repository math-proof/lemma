import Mathlib
import sympy.Basic
import sympy.integrals.transforms.FourierLaplace
open Fourier.FourierLaplace
open MeasureTheory


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


-- created on 2026-10-10
-- updated on 2026-10-24
