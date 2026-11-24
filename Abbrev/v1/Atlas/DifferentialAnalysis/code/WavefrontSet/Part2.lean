module
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Fourier.Convolution
public import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.HormanderFundamental
public import Def.v1.Atlas.DifferentialAnalysis.code.HormanderFundamental
public import Def.v1.Atlas.DifferentialAnalysis.code.WavefrontSet


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped SchwartzMap FourierTransform

open MeasureTheory Set

namespace ConeSupport

variable {n : ℕ}

/-- If `Γ ⊆ 𝕊ⁿ⁻¹` is closed and disjoint from the conic singular support of
`u`, then `u` admits a decomposition `u = u₁' + u₁'' + u₂` where `u₁'` is
compactly supported, `u₁''` vanishes on Schwartz functions whose nonzero
points all have direction in `Γ`, `u₂` is Schwartz, and the conic support of
`u₁' + u₁''` is disjoint from `Γ`. -/
abbrev schwEmbed : 𝓢(E n, ℂ) →L[ℂ] 𝓢'(E n, ℂ) :=
  SchwartzMap.toTemperedDistributionCLM (E n) ℂ

end ConeSupport
end
