import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Fourier.FourierLaplace

open Fourier.FourierLaplace
open MeasureTheory


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

-- created on 2026-10-10
