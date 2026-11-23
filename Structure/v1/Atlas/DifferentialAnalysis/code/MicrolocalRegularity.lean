/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MicrolocalRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.DifferentialAnalysis.code.WavefrontSet.Part3
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.WavefrontSet
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.ConeSupportCorollary
public import Theorem.v1.Atlas.DifferentialAnalysis.code.ConeSupportCorollary
public import Def.v1.Atlas.DifferentialAnalysis.code.MicrolocalRegularity


public noncomputable section

open scoped SchwartzMap

namespace WavefrontSet

variable {n : ℕ}


/-- Predicate that `ψ₁` acts as a conic cutoff separating conic singular supports `K₁` and `K₂`:
multiplying by `ψ₁` (resp. `1 - ψ₁`) kills the conic singular support of any distribution whose
`Css` lies in `K₂` (resp. `K₁`). -/
structure IsConicCutoffForDisjointCss (K₁ K₂ : Set (ClosedBall n))
    (ψ₁ : EuclideanSpace ℝ (Fin n) → ℂ) : Prop where
  schwartz_of_mul :
    ∀ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ), Css u₂ ⊆ K₂ →
      Css (TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂) = ∅
  schwartz_of_compl_mul :
    ∀ u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ), Css u₁ ⊆ K₁ →
      Css (TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁) = ∅

end WavefrontSet
end
