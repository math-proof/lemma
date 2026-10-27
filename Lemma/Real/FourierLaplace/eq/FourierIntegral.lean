import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Fourier.FourierLaplace
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


-- created on 2026-10-10
-- updated on 2026-10-26
