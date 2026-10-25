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
import Structure.v1.Atlas.DifferentialAnalysis.code.WavefrontSet.Part2


noncomputable section

open scoped SchwartzMap FourierTransform

open MeasureTheory Set

namespace ConeSupport

variable {n : ℕ}

variable {n}

variable {n : ℕ} {K₁ K₂ : Set (ConeSupport.E n)} (D : CssPairingData K₁ K₂)

open scoped SchwartzMap

/-- The `ψ`-pairing of `u₁` and `u₂` defined from `CssPairingData`:
`u₁(ψ·u₂) + u₂((1-ψ)·u₁)`, evaluated using the Schwartz representatives
produced by `toSchwartz`. -/
noncomputable def CssPairingData.pairingψ
    (u₁ : 𝓢'(ConeSupport.E n, ℂ)) (h₁ : D.Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(ConeSupport.E n, ℂ)) (h₂ : D.Css u₂ ⊆ K₂) : ℂ :=
  u₁ (D.toSchwartz _ (D.css_ψ_mul_empty u₂ h₂)) +
  u₂ (D.toSchwartz _ (D.css_ψ_compl_mul_empty u₁ h₁))

/-- The `ψ'`-pairing of `u₁` and `u₂` from `CssPairingData`: the variant of
`pairingψ` using `ψ'` in place of `ψ`. The symmetry axioms in
`CssPairingData` ensure `pairingψ = pairingψ'`. -/
noncomputable def CssPairingData.pairingψ'
    (u₁ : 𝓢'(ConeSupport.E n, ℂ)) (h₁ : D.Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(ConeSupport.E n, ℂ)) (h₂ : D.Css u₂ ⊆ K₂) : ℂ :=
  u₁ (D.toSchwartz _ (D.css_ψ'_mul_empty u₂ h₂)) +
  u₂ (D.toSchwartz _ (D.css_ψ'_compl_mul_empty u₁ h₁))

end Lemma12_5

end WavefrontSet

open scoped SchwartzMap FourierTransform

namespace WavefrontSet

variable {n : ℕ}

/-- `ProductWFscCondition u v` is the wavefront-set compatibility condition
ensuring that the pointwise product `u · v` of tempered distributions is
well-defined: for every base point `p` and every boundary frequency `ω`,
if `(p, ω) ∈ WFsc u` then `(p, -ω) ∉ WFsc v`. -/
def ProductWFscCondition (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∀ (p ω : ClosedBall n), ‖ω.val‖ = 1 →
    (p, ω) ∈ WFsc u → (p, -ω) ∉ WFsc v

/-- `ConvolutionWFscCondition u v` is the wavefront-set compatibility condition
ensuring that the convolution `u * v` of tempered distributions is well-defined:
for every boundary base direction `θ` and every frequency `q`, if `(θ, q) ∈ WFsc u`
then `(-θ, q) ∉ WFsc v`. Fourier-dual to `ProductWFscCondition`. -/
def ConvolutionWFscCondition (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∀ (θ q : ClosedBall n), ‖θ.val‖ = 1 →
    (θ, q) ∈ WFsc u → (-θ, q) ∉ WFsc v

end WavefrontSet
