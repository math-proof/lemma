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
import Structure.v1.Atlas.DifferentialAnalysis.code.WavefrontSet


noncomputable section

open scoped SchwartzMap FourierTransform

open MeasureTheory Set

namespace ConeSupport

variable {n : ℕ}

/-- If `ConicSingularSupportSphere u = ∅`, then `u` has the structure of an
empty conic singular support — it admits a Schwartz/compact decomposition
with the diff-compactness property. -/
def schwartzReflectionCLM : 𝓢(E n, ℂ) →L[ℂ] 𝓢(E n, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ)

/-- The convolution `u * φ` of a tempered distribution `u` with a Schwartz
function `φ`, defined as the tempered distribution `ψ ↦ u(φ̌ * ψ)` where
`φ̌(x) = φ(-x)`. -/
def schwartzConvolution
    (u : TemperedDistribution (E n) ℂ) (φ : 𝓢(E n, ℂ)) :
    TemperedDistribution (E n) ℂ :=
  u.comp ((SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)) (schwartzReflectionCLM φ))


/-- Convolution of a tempered distribution `v` with a Schwartz function `φ`,
viewed as a tempered distribution. -/
def schwDistribConv (v : 𝓢'(E n, ℂ)) (φ : 𝓢(E n, ℂ)) : 𝓢'(E n, ℂ) :=
  schwartzConvolution v φ

/-- Specialisation of `convolution_decomp_well_defined` to the standard
convolution system when the conic singular support of `u` is empty. -/
def sphereNeg (ω : Sphere n) : Sphere n :=
  ⟨-ω.1, mem_sphere_zero_iff_norm.mpr (by rw [norm_neg]; exact mem_sphere_zero_iff_norm.mp ω.2)⟩

/-- The image of a set `S ⊆ 𝕊ⁿ⁻¹` under the antipodal map. -/
def negSet (S : Set (Sphere n)) : Set (Sphere n) :=
  sphereNeg '' S

/-- The reflection of a tempered distribution `v`: the distribution
`φ ↦ v(φ ∘ -id)`. -/
def reflection (v : TemperedDistribution (E n) ℂ) :
    TemperedDistribution (E n) ℂ :=
  v.comp schwartzReflectionCLM


/-- If the conic-cutoff `g₀ · u` is already Schwartz, then `g₀ · (u * φ)` is also Schwartz
for any Schwartz `φ`. -/
def DisjointCssCondition (u v : TemperedDistribution (E n) ℂ) : Prop :=
  ∀ ω : Sphere n, ω ∈ ConicSingularSupportSphere u →
    sphereNeg ω ∉ ConicSingularSupportSphere v

end ConeSupport
end
