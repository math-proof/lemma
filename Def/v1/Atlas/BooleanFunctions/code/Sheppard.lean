module
public import Def.v1.Atlas.BooleanFunctions.code.Claim21Lec10
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Claim21Lec10
public import Def.v1.Atlas.BooleanFunctions.code.GaussianStability.Part2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Sheppard.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace GaussianStability

def signFn : ℝ → ℝ := fun x => if x ≥ 0 then 1 else -1

def gaussianNoiseStabilitySign (ρ : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, signFn p.1 * signFn p.2 ∂(rhoCorrelatedGaussian ρ)

end GaussianStability
end
