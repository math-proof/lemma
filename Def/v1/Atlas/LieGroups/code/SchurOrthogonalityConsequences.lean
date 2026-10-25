/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SchurOrthogonalityConsequences.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.SchurOrthogonality
import Lemma.Matrix.EqGetTraceSum
import Lemma.Complex.ConvolutionOp.eq.Integral_MulConvolutionKernel
import Abbrev.v1.Atlas.LieGroups.code.PlancherelCompact.Part3


noncomputable section

open MeasureTheory ContinuousRep

open scoped ComplexConjugate

section ConvolutionFormula

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsHaarMeasure]

def convolution (φ₁ φ₂ : K → ℂ) : K → ℂ :=
  fun z => ∫ y : K, φ₁ (z * y⁻¹) * φ₂ y ∂μ

def KFiniteFunctionSubspace :
    Submodule ℂ (K → ℂ) :=
  ⨆ (ρ : IrrFinDimRep K), MatrixCoefficientSubspace K ρ.rep

end ConvolutionFormula
end
