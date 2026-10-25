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
import Def.v1.Atlas.DifferentialAnalysis.code.WavefrontSet.Part5


noncomputable section

open scoped SchwartzMap FourierTransform

open MeasureTheory Set

namespace ConeSupport

variable {n : ℕ}

variable {n}

open ConeSupport in

/-- Data structure packaging the inputs needed to define the `Css`-pairing
`⟨u₁, u₂⟩` used in Lemma 12.5: a notion of cone support `Css`, two cutoff
functions `ψ, ψ'` together with hypotheses that the relevant products have
empty `Css`, a recipe `toSchwartz` for upgrading such tempered distributions
to Schwartz functions, plus linearity and symmetry compatibilities. -/
structure CssPairingData {n : ℕ} (K₁ K₂ : Set (ConeSupport.E n)) where
  Css : 𝓢'(ConeSupport.E n, ℂ) → Set (ConeSupport.E n)
  ψ  : ConeSupport.E n → ℂ
  ψ' : ConeSupport.E n → ℂ
  toSchwartz : (u : 𝓢'(ConeSupport.E n, ℂ)) → Css u = ∅ →
    SchwartzMap (ConeSupport.E n) ℂ
  css_ψ_mul_empty : ∀ u : 𝓢'(ConeSupport.E n, ℂ), Css u ⊆ K₂ →
    Css (TemperedDistribution.smulLeftCLM ℂ ψ u) = ∅
  css_ψ_compl_mul_empty : ∀ u : 𝓢'(ConeSupport.E n, ℂ), Css u ⊆ K₁ →
    Css (TemperedDistribution.smulLeftCLM ℂ (1 - ψ) u) = ∅
  css_ψ'_mul_empty : ∀ u : 𝓢'(ConeSupport.E n, ℂ), Css u ⊆ K₂ →
    Css (TemperedDistribution.smulLeftCLM ℂ ψ' u) = ∅
  css_ψ'_compl_mul_empty : ∀ u : 𝓢'(ConeSupport.E n, ℂ), Css u ⊆ K₁ →
    Css (TemperedDistribution.smulLeftCLM ℂ (1 - ψ') u) = ∅
  css_diff_empty₂ : ∀ u : 𝓢'(ConeSupport.E n, ℂ), Css u ⊆ K₂ →
    Css (TemperedDistribution.smulLeftCLM ℂ (ψ - ψ') u) = ∅
  css_diff_empty₁ : ∀ u : 𝓢'(ConeSupport.E n, ℂ), Css u ⊆ K₁ →
    Css (TemperedDistribution.smulLeftCLM ℂ (ψ - ψ') u) = ∅
  linearity_mul : ∀ (u₂ : 𝓢'(ConeSupport.E n, ℂ)) (h₂ : Css u₂ ⊆ K₂)
    (u₁ : 𝓢'(ConeSupport.E n, ℂ)),
    u₁ (toSchwartz _ (css_ψ_mul_empty u₂ h₂)) -
      u₁ (toSchwartz _ (css_ψ'_mul_empty u₂ h₂)) =
    u₁ (toSchwartz _ (css_diff_empty₂ u₂ h₂))
  linearity_compl : ∀ (u₁ : 𝓢'(ConeSupport.E n, ℂ)) (h₁ : Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(ConeSupport.E n, ℂ)),
    u₂ (toSchwartz _ (css_ψ'_compl_mul_empty u₁ h₁)) -
      u₂ (toSchwartz _ (css_ψ_compl_mul_empty u₁ h₁)) =
    u₂ (toSchwartz _ (css_diff_empty₁ u₁ h₁))
  symmetry_eval : ∀ (u₁ : 𝓢'(ConeSupport.E n, ℂ)) (h₁ : Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(ConeSupport.E n, ℂ)) (h₂ : Css u₂ ⊆ K₂),
    u₁ (toSchwartz _ (css_diff_empty₂ u₂ h₂)) =
    u₂ (toSchwartz _ (css_diff_empty₁ u₁ h₁))

end ConeSupport
end
