/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzRepresentation
public import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
public import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzRepresentation
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.TransferInstance
public import Mathlib.Analysis.Fourier.LpSpace

@[expose] public section

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
