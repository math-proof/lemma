/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Real.StarOrdered

open Matrix Real

noncomputable section

namespace Thm48

/-- Spiked covariance model: $\Sigma = \theta v v^\top + I_d$ with unit spike `v` and
`θ > 0`. -/
def IsSpikedCovariance {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (θ : ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : Prop :=
  0 < θ ∧ ‖v‖ = 1 ∧ S = θ • (vecMulVec v v) + (1 : Matrix (Fin d) (Fin d) ℝ)

/-- Principal angle between two vectors, $\arccos(|\langle u, v\rangle|)$. -/
noncomputable def principalAngle {d : ℕ}
    (u v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  arccos |@inner ℝ _ _ u v|

/-- Operator (spectral) norm of a square real matrix. -/
noncomputable def matrixOpNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖

/-- `w` is a (unit) leading eigenvector of `M`: it maximizes the Rayleigh quotient
$u^\top M u$ over unit vectors `u`. -/
def IsLargestEigenvector {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) : Prop :=
  ‖w‖ = 1 ∧
  ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
    dotProduct (EuclideanSpace.equiv (Fin d) ℝ u)
      (M.mulVec (EuclideanSpace.equiv (Fin d) ℝ u)) ≤
    dotProduct (EuclideanSpace.equiv (Fin d) ℝ w)
      (M.mulVec (EuclideanSpace.equiv (Fin d) ℝ w))
