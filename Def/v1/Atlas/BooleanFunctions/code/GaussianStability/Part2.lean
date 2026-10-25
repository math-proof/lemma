/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/GaussianStability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Structure.v1.Atlas.BooleanFunctions.code.GaussianStability


noncomputable section

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal

namespace GaussianStability

variable {n : ℕ}

def rhoCorrelatedGaussian (ρ : ℝ) : Measure (ℝ × ℝ) :=
  ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
    (fun p : ℝ × ℝ => (p.1, ρ * p.1 + Real.sqrt (1 - ρ ^ 2) * p.2))

def gaussianNoiseOperator (ρ : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ w, f (ρ • z + Real.sqrt (1 - ρ ^ 2) • w)
    ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))

def gaussianNoiseStability (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∫ x, f x * gaussianNoiseOperator ρ f x
    ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))

end GaussianStability
end
