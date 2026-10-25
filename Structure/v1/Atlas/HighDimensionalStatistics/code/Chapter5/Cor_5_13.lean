/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_13.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.ExponentialBounds
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory.Part3
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Lemma_5_3_5_4_5_8
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_3_5_4_5_8
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_13.Part2
open MeasureTheory InformationTheory


noncomputable section

namespace GaussianSequenceModel

/-- Structural property recording that a family `P : ℝ^d → Measure ℝ^d` is a Gaussian sequence
model with noise level `σ` and sample size `n`: each `P θ` is a probability measure with the
expected coordinate-wise variance, mean, KL/density-ratio structure, and integrability
properties required to run the minimax arguments of Chapter 5. -/
structure IsGSM {d : ℕ} (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (σ : ℝ) (n : ℕ) : Prop where
  isProbabilityMeasure : ∀ (hσ : 0 < σ) (hn : 0 < n) (θ : Fin d → ℝ),
    IsProbabilityMeasure (P θ)
  identity_risk_coord : ∀ (hσ : 0 < σ) (hn : 0 < n)
    (θ : Fin d → ℝ) (i : Fin d),
    ∫ Y, (Y i - θ i) ^ 2 ∂(P θ) = σ ^ 2 / ↑n
  coord_mean : ∀ (hσ : 0 < σ) (hn : 0 < n)
    (θ : Fin d → ℝ) (i : Fin d),
    ∫ Y, Y i ∂(P θ) = θ i
  density_ratio : ∀ (hσ : 0 < σ) (hn : 0 < n)
    (θ₁ θ₂ : Fin d → ℝ), P θ₁ = (P θ₂).withDensity (fun Y =>
      ENNReal.ofReal (Real.exp ((↑n / (2 * σ ^ 2)) *
        ∑ i : Fin d, ((Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2))))
  integrable_sqDist : ∀ (hσ : 0 < σ) (hn : 0 < n)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
    Integrable (fun Y => sqDist (θhat Y) θ) (P θ)
  bddAbove_risk : ∀ (hσ : 0 < σ) (hn : 0 < n)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
    BddAbove (Set.range fun θ => ⨆ (_ : θ ∈ (Set.univ : Set (Fin d → ℝ))),
      ∫ Y, sqDist (θhat Y) θ ∂(P θ))
  hP_kl_ne_top : ∀ (θ₀ θ₁ : Fin d → ℝ),
    InformationTheory.klDiv (P θ₁) (P θ₀) ≠ ⊤

  expected_cross_term_bound : ∀ (hσ : 0 < σ) (hn : 0 < n) (hd : 0 < d)
    (R : ℝ) (hR : 0 < R)
    (θ θ' : Fin d → ℝ)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ))
    (hθ' : l1norm θ' ≤ R)
    (hθhat : ∀ Y, l1norm (θhat Y) ≤ R),
    ∫ Y, ∑ i : Fin d, (θhat Y i - θ' i) * (Y i - θ i) ∂(P θ) ≤
      (σ ^ 2 / ↑n) * (R * Real.log ↑d / σ)
  integrable_cross_term : ∀ (hσ : 0 < σ) (hn : 0 < n)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ θ' : Fin d → ℝ),
    Integrable (fun Y => ∑ i : Fin d, (θhat Y i - θ' i) * (Y i - θ i)) (P θ)

end GaussianSequenceModel
end
