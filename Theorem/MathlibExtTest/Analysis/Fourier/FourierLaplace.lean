/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Fourier/FourierLaplace.lean -/


import Theorem.Analysis.Fourier.FourierLaplace
import Def.MathlibExtTest.Analysis.Fourier.FourierLaplace
open MeasureTheory


namespace FourierTest

example (f : ℝ → ℂ) (r : ℝ) :
    Fourier.fourierLaplace f r =
      Fourier.fourierIntegral Real.fourierChar volume f r :=
  Fourier.fourierLaplace_ofReal f r

example (f : ℝ → ℂ) : Fourier.fourierLaplace f 0 = ∫ x, f x := by
  simp

example (z : ℂ) : Fourier.fourierLaplace 0 z = 0 := by
  simp

example : Differentiable ℂ (Fourier.fourierLaplace compactlySupportedExample) :=
  Fourier.differentiable_fourierLaplace compactlySupportedExample_integrable
    compactlySupportedExample_hasCompactSupport

example (z : ℂ) :
    HasDerivAt (Fourier.fourierLaplace compactlySupportedExample)
      (∫ x : ℝ, compactlySupportedExample x *
        ((-2 * (Real.pi : ℂ) * Complex.I * x) *
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * x * z))) z :=
  Fourier.hasDerivAt_fourierLaplace compactlySupportedExample_integrable
    compactlySupportedExample_hasCompactSupport z

end FourierTest
