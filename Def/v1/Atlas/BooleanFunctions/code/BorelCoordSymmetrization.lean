/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/BorelCoordSymmetrization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.BooleanFunctions.code.BorelOneD
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.BorelOneD


noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace GaussianStability

variable {n : ℕ}

def EuclideanSpace.updateCoord (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) (t : ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm
    (Function.update ((WithLp.equiv 2 (Fin n → ℝ)) x) i t)

def conditionalMean (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ t, f (EuclideanSpace.updateCoord x i t) ∂(gaussianReal 0 1)

def symmetrize_coord (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => thresholdFn (conditionalMean i f x) (x i)

def fiberNoiseStability1D (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ t, (f (EuclideanSpace.updateCoord x i t)) *
    (∫ z, f (EuclideanSpace.updateCoord x i (ρ * t + √(1 - ρ^2) * z))
      ∂(gaussianReal 0 1))
    ∂(gaussianReal 0 1)

def fiberNoiseStability1D_symmetrized (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ t, (thresholdFn (conditionalMean i f x) t) *
    (∫ z, (thresholdFn (conditionalMean i f x)) (ρ * t + √(1 - ρ^2) * z)
      ∂(gaussianReal 0 1))
    ∂(gaussianReal 0 1)

end GaussianStability
end
