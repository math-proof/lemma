/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzRepresentation
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzRepresentation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.TransferInstance
import Mathlib.Analysis.Fourier.LpSpace
open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap


noncomputable section

namespace FourierInversion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section Isomorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The Fourier transform as a continuous `ℂ`-linear equivalence on the
Schwartz space `𝓢(V, E)`. -/
def fourierSchwartzCLE : 𝓢(V, E) ≃L[ℂ] 𝓢(V, E) :=
  FourierTransform.fourierCLE ℂ 𝓢(V, E)

/-- The Fourier transform on tempered distributions packaged as a `ℂ`-linear
equivalence `𝓢'(E, F) ≃ₗ[ℂ] 𝓢'(E, F)`. -/
def fourierTemperedDistributionEquiv : 𝓢'(E, F) ≃ₗ[ℂ] 𝓢'(E, F) :=
  fourierEquiv ℂ 𝓢'(E, F)

end Isomorphism
end FourierInversion
end
