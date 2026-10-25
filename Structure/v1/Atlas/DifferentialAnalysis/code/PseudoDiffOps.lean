/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ConvolutionTheorem
import Def.v1.Atlas.DifferentialAnalysis.code.ConvolutionTheorem
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyCompact
import Def.v1.Atlas.DifferentialAnalysis.code.PseudoDiffOps.Part2


noncomputable section

open scoped SchwartzMap Pointwise

open MeasureTheory Set Function TemperedDistribution

namespace DifferentialOperators

variable {n : ℕ}

/-- A decomposition of a tempered distribution `u = singular + smooth` into a singular
part with compact support contained in `supportSet` and a globally smooth, compactly
supported part. Used in the proof of `singularSupport_convolution_subset`. -/
structure SmoothDecomp (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) where
  singular : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)
  smooth : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)
  supportSet : Set (EuclideanSpace ℝ (Fin n))
  supportSet_compact : IsCompact supportSet
  singular_supported :
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (Function.support (⇑φ) ∩ supportSet = ∅) → singular φ = 0
  singular_compactSupport : HasCompactSupport singular
  smooth_isSmooth : ∀ x₀ : EuclideanSpace ℝ (Fin n), isSmoothNear smooth x₀
  smooth_compactSupport : HasCompactSupport smooth
  sum_eq : u = singular + smooth

end DifferentialOperators
end
