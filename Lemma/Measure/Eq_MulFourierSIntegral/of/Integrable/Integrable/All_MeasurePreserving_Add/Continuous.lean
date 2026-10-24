import Mathlib
import sympy.Basic
import sympy.integrals.transforms.ConvolutionTheorem

open scoped Convolution

/--
[ConvolutionTheorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/ConvolutionTheorem.lean)
-/
@[path]
private lemma convolution_theorem_eq
-- given
  {e : AddChar ℝ Circle}
  {μ : MeasureTheory.Measure ℝ} [MeasureTheory.SigmaFinite μ]
  {f g : ℝ → ℂ}
  (he : Continuous e)
  (hinv : ∀ a : ℝ, MeasureTheory.MeasurePreserving (fun x => a + x) μ μ)
  (hf : MeasureTheory.Integrable f μ)
  (hg : MeasureTheory.Integrable g μ)
  (w : ℝ) :
-- imply
  Fourier.fourierIntegral e μ
    (f ⋆[ContinuousLinearMap.lsmul ℂ ℂ, μ] g) w =
    Fourier.fourierIntegral e μ f w * Fourier.fourierIntegral e μ g w := by
-- proof
  apply Measure.Eq_MulFourierSIntegral.of.Integrable.Integrable.All_MeasurePreserving_Add.Continuous.convolution_theorem he hinv hf hg w

-- created on 2026-10-10
