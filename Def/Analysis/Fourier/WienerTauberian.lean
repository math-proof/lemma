/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/WienerTauberian.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

open MeasureTheory
open scoped Convolution FourierTransform


namespace MathlibExt.Analysis.Fourier.WienerWanted

-- Modulated dilations.
noncomputable def wtaubModDil (V : ℝ → ℂ) (w₀ δ : ℝ) : ℝ → ℂ :=
  fun x => ((Real.fourierChar (w₀ * x) : Circle) : ℂ) * ((δ : ℂ) * V (δ * x))

noncomputable def wtaubDil (W : ℝ → ℂ) (lam : ℝ) : ℝ → ℂ :=
  fun x => (lam : ℂ) * W (lam * x)

end MathlibExt.Analysis.Fourier.WienerWanted
