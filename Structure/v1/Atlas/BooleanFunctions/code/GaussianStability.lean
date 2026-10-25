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
import Def.v1.Atlas.BooleanFunctions.code.GaussianStability


noncomputable section

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal

namespace GaussianStability

variable {n : ℕ}

structure IsRhoCorrelated {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y : Ω → ℝ) (ρ : ℝ) : Prop where
  rho_mem : ρ ∈ Set.Icc (-1 : ℝ) 1
  hX_meas : Measurable X
  hY_meas : Measurable Y
  hX_dist : μ.map X = gaussianReal 0 1
  hY_dist : μ.map Y = gaussianReal 0 1
  hXY_corr : ∫ ω, X ω * Y ω ∂μ = ρ

end GaussianStability
end
