/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierGaussian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic


noncomputable section

open Real MeasureTheory Complex

open scoped RealInnerProductSpace

namespace FourierAnalysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier transform as defined in Melrose's book: `(Ff)(w) = ∫ e^{-i⟨v,w⟩} f(v) dv`,
on a real finite-dimensional inner product space `V`. -/
def bookFourierTransform (f : V → ℂ) (w : V) : ℂ :=
  ∫ v, cexp (-(I : ℂ) * ↑(⟪v, w⟫)) * f v

end FourierAnalysis
end
