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
public import Def.v1.Atlas.DifferentialAnalysis.code.FourierInversion
open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap

public section

noncomputable section

namespace FourierInversion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section Isomorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Fourier inversion on tempered distributions: `𝓕⁻(𝓕 u) = u`. -/
@[simp]
theorem fourier_inverse_left (u : 𝓢'(E, F)) : 𝓕⁻ (𝓕 u) = u :=
  fourierInv_fourier_eq u

/-- Fourier inversion on tempered distributions: `𝓕(𝓕⁻ u) = u`. -/
theorem fourier_inverse_right (u : 𝓢'(E, F)) : 𝓕 (𝓕⁻ u) = u :=
  fourier_fourierInv_eq u

end Isomorphism
end FourierInversion
end
