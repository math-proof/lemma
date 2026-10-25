/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Def_4_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Def_1_2
open MeasureTheory Matrix Real Finset


noncomputable section

/-- The operator (spectral) norm of a real matrix, defined via the associated continuous
linear map on Euclidean spaces. -/
def matrixOpNorm {d T : ℕ} (A : Matrix (Fin d) (Fin T) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖

/-- A random matrix `F : Ω → Matrix (Fin d) (Fin T) ℝ` is *sub-Gaussian with proxy
variance* `σsq` if for every pair of unit vectors `u ∈ ℝ^d`, `v ∈ ℝ^T`, the random scalar
$u^\top F v$ is sub-Gaussian with proxy variance `σsq`. -/
def IsSubGaussianMatrix {Ω : Type*} [MeasurableSpace Ω] {d T : ℕ}
    (F : Ω → Matrix (Fin d) (Fin T) ℝ) (σsq : ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (u : EuclideanSpace ℝ (Fin d)) (v : EuclideanSpace ℝ (Fin T)),
    ‖u‖ = 1 → ‖v‖ = 1 →
    IsSubGaussian (fun ω => dotProduct (EuclideanSpace.equiv (Fin d) ℝ u)
      ((F ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ v))) σsq μ

end
