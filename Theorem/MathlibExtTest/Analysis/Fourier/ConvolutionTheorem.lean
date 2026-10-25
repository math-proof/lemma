/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Fourier/ConvolutionTheorem.lean -/


import sympy.atlas.Analysis.Measure.Eq_MulFourierSIntegral.of.Integrable.Integrable.All_MeasurePreserving_Add.Continuous
open MeasureTheory
open scoped Convolution


namespace MetaMathlibExt

-- The abstract result recovers the standard Fourier convolution theorem on `ℝ`.
example {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (w : ℝ) :
    Fourier.fourierIntegral Real.fourierChar volume
        (f ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] g) w =
      Fourier.fourierIntegral Real.fourierChar volume f w *
        Fourier.fourierIntegral Real.fourierChar volume g w := by
  exact convolution_theorem Real.continuous_fourierChar
    (fun a => measurePreserving_add_left volume a) hf hg w

end MetaMathlibExt
