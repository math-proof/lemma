/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/WienerTauberian.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Lemma.Real.Fourier_UFnMul.eq.SMulFourier.of.Ne_0
import Lemma.Real.Fourier_UFnMul.eq.SMulFourier.of.Gt_0
import Lemma.Real.Fourier_Coe_UFnMul.eq.SMulFourier.of.Gt_0
open MeasureTheory
open scoped Convolution FourierTransform


namespace MathlibExt.Analysis.Fourier.WienerWanted

-- Modulated dilations.
noncomputable def wtaubModDil (V : ℝ → ℂ) (w₀ δ : ℝ) : ℝ → ℂ :=
  fun x => ((Real.fourierChar (w₀ * x) : Circle) : ℂ) * ((δ : ℂ) * V (δ * x))

noncomputable def wtaubDil (W : ℝ → ℂ) (lam : ℝ) : ℝ → ℂ :=
  fun x => (lam : ℂ) * W (lam * x)

end MathlibExt.Analysis.Fourier.WienerWanted
