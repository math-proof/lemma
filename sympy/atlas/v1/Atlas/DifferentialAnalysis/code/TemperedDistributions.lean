/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TemperedDistributions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.Support

noncomputable section

open scoped SchwartzMap ENNReal NNReal LineDeriv
open SchwartzMap MeasureTheory ContinuousLinearMap

namespace TemperedDistributions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Continuous embedding `Lp(F, μ) → 𝓢'(E, F)` sending an `Lᵖ`-function to the tempered
distribution it represents. -/
def lpToTemperedDistributionCLM
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace F]
    (μ : Measure E) [μ.HasTemperateGrowth]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp F p μ →L[ℂ] 𝓢'(E, F) :=
  Lp.toTemperedDistributionCLM F μ p

/-- Distributional directional derivative in direction `m`: a continuous linear endomorphism
of `𝓢'(E, F)` given by `u ↦ u ∘ (-∂_m)`. -/
def distribDerivCLM (m : E) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  LineDeriv.lineDerivOpCLM ℂ (𝓢'(E, F)) m

/-- Distributional multiplication by a (necessarily temperate) function `g : E → ℂ`, as a
continuous linear endomorphism of `𝓢'(E, F)`. -/
def distribMulCLM (g : E → ℂ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  TemperedDistribution.smulLeftCLM F g

/-- Continuous linear operator on `𝓢(ℝ, G)` given by `f ↦ x^α · f^(β)`, i.e. the multiplication
by the monomial `xᵅ` composed with `β`-fold differentiation. -/
def SchwartzMap.polyMulDerivCLM (α β : ℕ) :
    𝓢(ℝ, G) →L[ℝ] 𝓢(ℝ, G) :=
  SchwartzMap.smulLeftCLM G (fun x : ℝ => x ^ α) ∘L (SchwartzMap.derivCLM ℝ G) ^ β

end Lemma71

section Lemma74

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 G] [SMulCommClass ℝ 𝕜 G]
