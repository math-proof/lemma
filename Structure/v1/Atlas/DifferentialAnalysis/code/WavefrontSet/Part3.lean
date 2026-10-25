/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Fourier.Convolution
import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.HormanderFundamental
import Def.v1.Atlas.DifferentialAnalysis.code.HormanderFundamental
import Def.v1.Atlas.DifferentialAnalysis.code.WavefrontSet.Part6
open scoped SchwartzMap FourierTransform


namespace WavefrontSet

variable {n : ℕ}

/-- Data witnessing that `u, v` can be convolved: a finite decomposition
`u = Σ uPart i + remainder`, `v = Σ vPart j` whose pairwise conic singular supports
satisfy the disjointness condition required for `ConeSupport.convolution_of_disjointCss`,
together with a remainder term `remainderConv` that handles the diagonal/leftover
contribution. -/
structure ConvolutionDecompData {n : ℕ}
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) where
  ι : Type
  [finι : Fintype ι]
  [decι : DecidableEq ι]
  uPart : ι → TemperedDistribution (ConeSupport.E n) ℂ
  vPart : ι → TemperedDistribution (ConeSupport.E n) ℂ
  disjCss : ∀ i j : ι, ConeSupport.DisjointCssCondition (uPart i) (vPart j)
  remainderConv : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)

attribute [instance] ConvolutionDecompData.finι ConvolutionDecompData.decι

/-- The total convolution coming from a `ConvolutionDecompData`: sum of the
pairwise convolutions `convolution_of_disjointCss (uPart i) (vPart j)` plus the
remainder term. -/
structure ConicPartitionData {n : ℕ}
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) where
  ι : Type
  [finι : Fintype ι]
  [decι : DecidableEq ι]
  uPart : ι → TemperedDistribution (ConeSupport.E n) ℂ
  vPart : ι → TemperedDistribution (ConeSupport.E n) ℂ
  angSupp : ι → Set (ConeSupport.Sphere n)
  angSupp_closed : ∀ i, IsClosed (angSupp i)
  css_uPart_sub : ∀ i, ConeSupport.ConicSingularSupportSphere (uPart i) ⊆ angSupp i
  css_vPart_sub : ∀ i, ConeSupport.ConicSingularSupportSphere (vPart i) ⊆ angSupp i
  angSupp_neg_disjoint : ∀ i j,
    Disjoint (angSupp i) (ConeSupport.negSet (angSupp j))
  remainderConv : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)

end WavefrontSet
